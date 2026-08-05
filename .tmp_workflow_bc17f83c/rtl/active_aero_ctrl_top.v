module active_aero_ctrl_top (
    input clk,
    input reset_n,
    input [2:0] cfg_geometry_source,
    input [2:0] cfg_geometry_format,
    input [15:0] cfg_geometry_id,
    input [15:0] stream_velocity_mps,
    input flow_valid,
    output req_valid,
    output [15:0] req_id,
    output [2:0] req_geometry_source,
    output [2:0] req_geometry_format,
    output [15:0] req_geometry_id,
    output [15:0] req_stream_velocity_mps,
    output req_flow_valid,
    input rsp_valid,
    input [15:0] rsp_id,
    input [23:0] drag_force,
    input [23:0] lift_force,
    input [23:0] surface_pressure,
    input flow_field_valid,
    input [15:0] flow_field_meta,
    output [15:0] actuator_cmd,
    output actuator_valid,
    output fallback_active,
    output stale_reject,
    output timeout_fault,
    output cmd_clamped,
    output [2:0] status_code,
    output [2:0] fault_code,
    output [15:0] trace_req_id,
    output [15:0] trace_rsp_id,
    input cfg_clear_sticky_faults
);

    localparam [2:0] STATUS_IDLE = 3'd0;
    localparam [2:0] STATUS_PENDING = 3'd1;
    localparam [2:0] STATUS_ACCEPTED = 3'd2;
    localparam [2:0] STATUS_FALLBACK = 3'd3;
    localparam [2:0] STATUS_FAULTED = 3'd4;

    localparam [2:0] FAULT_NONE = 3'd0;
    localparam [2:0] FAULT_STALE = 3'd1;
    localparam [2:0] FAULT_TIMEOUT = 3'd2;
    localparam [2:0] FAULT_ENVELOPE = 3'd3;
    localparam [2:0] FAULT_INTEGRITY = 3'd4;
    localparam [2:0] FAULT_CLAMP = 3'd5;

    localparam [15:0] SAFE_DEFAULT_CMD = 16'h0000;
    localparam [15:0] TIMEOUT_CFG_RESET = 16'd32;
    localparam [15:0] VEL_MIN_CFG_RESET = 16'd20;
    localparam [15:0] VEL_MAX_CFG_RESET = 16'd55;
    localparam [15:0] ACT_MIN_CFG_RESET = 16'd0;
    localparam [15:0] ACT_MAX_CFG_RESET = 16'd255;
    localparam [15:0] RATE_LIMIT_CFG_RESET = 16'd0;

    reg [2:0] status_code_r;
    reg [2:0] fault_code_r;
    reg [15:0] req_id_r;
    reg [15:0] trace_rsp_id_r;
    reg [15:0] trace_req_id_r;
    reg [15:0] actuator_cmd_r;
    reg actuator_valid_r;
    reg fallback_active_r;
    reg stale_reject_r;
    reg timeout_fault_r;
    reg cmd_clamped_r;
    reg pending_r;
    reg [15:0] timeout_counter_r;
    reg [15:0] cfg_timeout_count_r;
    reg [15:0] cfg_vel_min_r;
    reg [15:0] cfg_vel_max_r;
    reg [15:0] cfg_act_min_r;
    reg [15:0] cfg_act_max_r;
    reg [15:0] cfg_rate_limit_delta_r;
    reg [15:0] sample_velocity_r;
    reg [2:0] cfg_geometry_source_r;
    reg [2:0] cfg_geometry_format_r;
    reg [15:0] cfg_geometry_id_r;
    reg [15:0] prev_actuator_cmd_r;
    reg [15:0] latched_drag_force_r;
    reg [15:0] latched_lift_force_r;
    reg [15:0] latched_surface_pressure_r;
    reg flow_valid_r;
    reg flow_field_valid_r;
    reg integrity_ok_r;
    reg [15:0] next_req_id;
    reg [15:0] response_metric;
    reg [15:0] raw_candidate;
    reg [15:0] limited_candidate;
    reg [15:0] clamped_candidate;
    reg [15:0] delta_mag;
    reg [15:0] abs_prev;
    reg [15:0] abs_diff;
    reg [15:0] timeout_limit;
    reg envelope_ok;
    reg response_match;
    reg response_qual_ok;
    reg response_accept;
    reg stale_event;
    reg timeout_event;
    reg envelope_event;
    reg integrity_event;
    reg clamp_event;
    reg clear_sticky;
    reg [15:0] drag_lo;
    reg [15:0] lift_lo;
    reg [15:0] pressure_lo;

    always @(*) begin
        status_code_r = STATUS_IDLE;
        fault_code_r = FAULT_NONE;
        next_req_id = req_id_r + 16'd1;
        response_metric = 16'd0;
        raw_candidate = 16'd0;
        limited_candidate = 16'd0;
        clamped_candidate = 16'd0;
        delta_mag = 16'd0;
        abs_prev = 16'd0;
        abs_diff = 16'd0;
        timeout_limit = cfg_timeout_count_r;
        envelope_ok = 1'b0;
        response_match = 1'b0;
        response_qual_ok = 1'b0;
        response_accept = 1'b0;
        stale_event = 1'b0;
        timeout_event = 1'b0;
        envelope_event = 1'b0;
        integrity_event = 1'b0;
        clamp_event = 1'b0;
        clear_sticky = cfg_clear_sticky_faults;
        drag_lo = {8'd0, drag_force[7:0]};
        lift_lo = {8'd0, lift_force[7:0]};
        pressure_lo = {8'd0, surface_pressure[7:0]};

        envelope_ok = flow_valid_r && (sample_velocity_r >= cfg_vel_min_r) && (sample_velocity_r <= cfg_vel_max_r);
        response_match = pending_r && rsp_valid && (rsp_id == req_id_r);
        response_qual_ok = flow_field_valid && (flow_field_meta != 16'd0) && (drag_force != 24'd0 || lift_force != 24'd0 || surface_pressure != 24'd0);
        response_accept = response_match && response_qual_ok && !timeout_fault_r && !stale_reject_r && envelope_ok;
        stale_event = pending_r && rsp_valid && (rsp_id != req_id_r);
        timeout_event = pending_r && (timeout_counter_r == 16'd0) && !response_accept;
        envelope_event = flow_valid_r && !envelope_ok;
        integrity_event = response_match && !response_qual_ok;
        response_metric = drag_lo + lift_lo + pressure_lo;
        raw_candidate = response_metric ^ cfg_geometry_id_r;
        raw_candidate = raw_candidate + cfg_geometry_source_r;
        raw_candidate = raw_candidate + cfg_geometry_format_r;
        if (raw_candidate < cfg_act_min_r) begin
            limited_candidate = cfg_act_min_r;
            clamp_event = 1'b1;
        end else if (raw_candidate > cfg_act_max_r) begin
            limited_candidate = cfg_act_max_r;
            clamp_event = 1'b1;
        end else begin
            limited_candidate = raw_candidate;
        end

        if (cfg_rate_limit_delta_r != 16'd0) begin
            if (limited_candidate > prev_actuator_cmd_r) begin
                delta_mag = limited_candidate - prev_actuator_cmd_r;
                if (delta_mag > cfg_rate_limit_delta_r) begin
                    clamped_candidate = prev_actuator_cmd_r + cfg_rate_limit_delta_r;
                    clamp_event = 1'b1;
                end else begin
                    clamped_candidate = limited_candidate;
                end
            end else begin
                abs_prev = prev_actuator_cmd_r;
                abs_diff = abs_prev - limited_candidate;
                if (abs_diff > cfg_rate_limit_delta_r) begin
                    if (prev_actuator_cmd_r > cfg_rate_limit_delta_r) begin
                        clamped_candidate = prev_actuator_cmd_r - cfg_rate_limit_delta_r;
                    end else begin
                        clamped_candidate = 16'd0;
                    end
                    clamp_event = 1'b1;
                end else begin
                    clamped_candidate = limited_candidate;
                end
            end
        end else begin
            clamped_candidate = limited_candidate;
        end

        if (!reset_n) begin
            status_code_r = STATUS_FALLBACK;
            fault_code_r = FAULT_NONE;
        end else if (pending_r) begin
            status_code_r = STATUS_PENDING;
        end else if (fallback_active_r) begin
            status_code_r = STATUS_FALLBACK;
        end else if (response_accept) begin
            status_code_r = STATUS_ACCEPTED;
        end else begin
            status_code_r = STATUS_IDLE;
        end

        if (stale_event) begin
            fault_code_r = FAULT_STALE;
        end else if (timeout_event) begin
            fault_code_r = FAULT_TIMEOUT;
        end else if (envelope_event) begin
            fault_code_r = FAULT_ENVELOPE;
        end else if (integrity_event) begin
            fault_code_r = FAULT_INTEGRITY;
        end else if (clamp_event) begin
            fault_code_r = FAULT_CLAMP;
        end else begin
            fault_code_r = FAULT_NONE;
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            cfg_geometry_source_r <= 3'd0;
            cfg_geometry_format_r <= 3'd0;
            cfg_geometry_id_r <= 16'd0;
            sample_velocity_r <= 16'd0;
            flow_valid_r <= 1'b0;
            flow_field_valid_r <= 1'b0;
            req_id_r <= 16'd0;
            trace_req_id_r <= 16'd0;
            trace_rsp_id_r <= 16'd0;
            actuator_cmd_r <= SAFE_DEFAULT_CMD;
            prev_actuator_cmd_r <= SAFE_DEFAULT_CMD;
            actuator_valid_r <= 1'b0;
            fallback_active_r <= 1'b1;
            stale_reject_r <= 1'b0;
            timeout_fault_r <= 1'b0;
            cmd_clamped_r <= 1'b0;
            pending_r <= 1'b0;
            timeout_counter_r <= 16'd0;
            cfg_timeout_count_r <= TIMEOUT_CFG_RESET;
            cfg_vel_min_r <= VEL_MIN_CFG_RESET;
            cfg_vel_max_r <= VEL_MAX_CFG_RESET;
            cfg_act_min_r <= ACT_MIN_CFG_RESET;
            cfg_act_max_r <= ACT_MAX_CFG_RESET;
            cfg_rate_limit_delta_r <= RATE_LIMIT_CFG_RESET;
            latched_drag_force_r <= 16'd0;
            latched_lift_force_r <= 16'd0;
            latched_surface_pressure_r <= 16'd0;
            integrity_ok_r <= 1'b0;
        end else begin
            cfg_geometry_source_r <= cfg_geometry_source;
            cfg_geometry_format_r <= cfg_geometry_format;
            cfg_geometry_id_r <= cfg_geometry_id;
            sample_velocity_r <= stream_velocity_mps;
            flow_valid_r <= flow_valid;
            flow_field_valid_r <= flow_field_valid;

            if (cfg_clear_sticky_faults) begin
                stale_reject_r <= 1'b0;
                timeout_fault_r <= 1'b0;
            end

            if (flow_valid && ((stream_velocity_mps < cfg_vel_min_r) || (stream_velocity_mps > cfg_vel_max_r))) begin
                fallback_active_r <= 1'b1;
            end

            if (flow_valid && (stream_velocity_mps >= cfg_vel_min_r) && (stream_velocity_mps <= cfg_vel_max_r) && !pending_r && !fallback_active_r) begin
                req_id_r <= next_req_id;
                trace_req_id_r <= next_req_id;
                pending_r <= 1'b1;
                timeout_counter_r <= cfg_timeout_count_r;
            end else if (pending_r) begin
                if (response_accept) begin
                    pending_r <= 1'b0;
                    trace_rsp_id_r <= rsp_id;
                    latched_drag_force_r <= drag_force[15:0];
                    latched_lift_force_r <= lift_force[15:0];
                    latched_surface_pressure_r <= surface_pressure[15:0];
                    actuator_cmd_r <= clamped_candidate;
                    prev_actuator_cmd_r <= clamped_candidate;
                    actuator_valid_r <= 1'b1;
                    fallback_active_r <= 1'b0;
                    integrity_ok_r <= 1'b1;
                    cmd_clamped_r <= clamp_event;
                    timeout_counter_r <= 16'd0;
                end else begin
                    actuator_valid_r <= 1'b0;
                    cmd_clamped_r <= 1'b0;
                    integrity_ok_r <= 1'b0;
                    if (rsp_valid && (rsp_id != req_id_r)) begin
                        stale_reject_r <= 1'b1;
                        fallback_active_r <= 1'b1;
                        pending_r <= 1'b0;
                        timeout_counter_r <= 16'd0;
                    end else if (timeout_counter_r == 16'd0) begin
                        timeout_fault_r <= 1'b1;
                        fallback_active_r <= 1'b1;
                        pending_r <= 1'b0;
                        timeout_counter_r <= 16'd0;
                    end else begin
                        timeout_counter_r <= timeout_counter_r - 16'd1;
                    end
                end
            end else begin
                actuator_valid_r <= 1'b0;
                cmd_clamped_r <= 1'b0;
                integrity_ok_r <= 1'b0;
                if (!((flow_valid && (stream_velocity_mps >= cfg_vel_min_r) && (stream_velocity_mps <= cfg_vel_max_r)) && !fallback_active_r)) begin
                    actuator_cmd_r <= SAFE_DEFAULT_CMD;
                    prev_actuator_cmd_r <= SAFE_DEFAULT_CMD;
                end
            end

            if (cfg_rate_limit_delta_r != cfg_rate_limit_delta_r) begin
                cfg_rate_limit_delta_r <= cfg_rate_limit_delta_r;
            end

            if (flow_valid) begin
                if (stream_velocity_mps < cfg_vel_min_r || stream_velocity_mps > cfg_vel_max_r) begin
                    fallback_active_r <= 1'b1;
                end
            end

            if (clamp_event && response_accept) begin
                cmd_clamped_r <= 1'b1;
            end

            if (stale_reject_r || timeout_fault_r || (flow_valid && ((stream_velocity_mps < cfg_vel_min_r) || (stream_velocity_mps > cfg_vel_max_r)))) begin
                fallback_active_r <= 1'b1;
            end

            if (cfg_clear_sticky_faults) begin
                if (!stale_reject_r && !timeout_fault_r && !pending_r && (stream_velocity_mps >= cfg_vel_min_r) && (stream_velocity_mps <= cfg_vel_max_r)) begin
                    fallback_active_r <= 1'b0;
                end
            end
        end
    end

    assign req_valid = pending_r ? 1'b1 : ((flow_valid && (stream_velocity_mps >= cfg_vel_min_r) && (stream_velocity_mps <= cfg_vel_max_r) && !fallback_active_r && !pending_r) ? 1'b1 : 1'b0);
    assign req_id = req_id_r;
    assign req_geometry_source = cfg_geometry_source_r;
    assign req_geometry_format = cfg_geometry_format_r;
    assign req_geometry_id = cfg_geometry_id_r;
    assign req_stream_velocity_mps = sample_velocity_r;
    assign req_flow_valid = flow_valid_r;
    assign actuator_cmd = fallback_active_r ? SAFE_DEFAULT_CMD : actuator_cmd_r;
    assign actuator_valid = actuator_valid_r & ~fallback_active_r;
    assign fallback_active = fallback_active_r;
    assign stale_reject = stale_reject_r;
    assign timeout_fault = timeout_fault_r;
    assign cmd_clamped = cmd_clamped_r;
    assign status_code = status_code_r;
    assign fault_code = fault_code_r;
    assign trace_req_id = trace_req_id_r;
    assign trace_rsp_id = trace_rsp_id_r;

endmodule
