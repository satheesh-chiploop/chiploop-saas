module aero_supervisor(
    clk,
    rst_n,
    tick_1ms,
    cfg_enable,
    cfg_stream_velocity_mps_setpoint,
    cfg_velocity_min_limit,
    cfg_velocity_max_limit,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_actuator_safe_position,
    cfg_command_timeout_cycles,
    cfg_max_slew_rate,
    cfg_geometry_format_id,
    cfg_geometry_source_id,
    cfg_geometry_version,
    cfg_clear_faults,
    stream_velocity_mps,
    geom_valid,
    geom_format_id_in,
    geom_source_id_in,
    geom_version_in,
    req_ready,
    rsp_valid,
    rsp_seq,
    rsp_drag_force,
    rsp_lift_force,
    rsp_surface_pressure,
    rsp_flow_field,
    rsp_inference_status_not_executed,
    req_valid,
    req_seq,
    req_inflight,
    current_state,
    fault_code,
    stale_reject_count,
    clamp_event_count,
    fallback_active,
    last_accepted_seq,
    last_response_age,
    model_response_valid_seen,
    request_age_cycles,
    request_stale,
    geometry_invalid,
    out_of_range_fault,
    sequence_mismatch_fault,
    service_unavailable_fault,
    protocol_error_fault,
    stale_response_fault
);
input clk;
input rst_n;
input tick_1ms;
input cfg_enable;
input [15:0] cfg_stream_velocity_mps_setpoint;
input [15:0] cfg_velocity_min_limit;
input [15:0] cfg_velocity_max_limit;
input [15:0] cfg_actuator_min_limit;
input [15:0] cfg_actuator_max_limit;
input [15:0] cfg_actuator_safe_position;
input [15:0] cfg_command_timeout_cycles;
input [15:0] cfg_max_slew_rate;
input [7:0] cfg_geometry_format_id;
input [7:0] cfg_geometry_source_id;
input [15:0] cfg_geometry_version;
input cfg_clear_faults;
input [15:0] stream_velocity_mps;
input geom_valid;
input [7:0] geom_format_id_in;
input [7:0] geom_source_id_in;
input [15:0] geom_version_in;
input req_ready;
input rsp_valid;
input [15:0] rsp_seq;
input [15:0] rsp_drag_force;
input [15:0] rsp_lift_force;
input [15:0] rsp_surface_pressure;
input [15:0] rsp_flow_field;
input rsp_inference_status_not_executed;
output req_valid;
output [15:0] req_seq;
output req_inflight;
output [3:0] current_state;
output [3:0] fault_code;
output [15:0] stale_reject_count;
output [15:0] clamp_event_count;
output fallback_active;
output [15:0] last_accepted_seq;
output [15:0] last_response_age;
output model_response_valid_seen;
output [15:0] request_age_cycles;
output request_stale;
output geometry_invalid;
output out_of_range_fault;
output sequence_mismatch_fault;
output service_unavailable_fault;
output protocol_error_fault;
output stale_response_fault;
reg req_valid;
reg [15:0] req_seq;
reg req_inflight;
reg [3:0] current_state;
reg [3:0] fault_code;
reg [15:0] stale_reject_count;
reg [15:0] clamp_event_count;
reg fallback_active;
reg [15:0] last_accepted_seq;
reg [15:0] last_response_age;
reg model_response_valid_seen;
reg [15:0] request_age_cycles;
reg request_stale;
reg geometry_invalid;
reg out_of_range_fault;
reg sequence_mismatch_fault;
reg service_unavailable_fault;
reg protocol_error_fault;
reg stale_response_fault;
reg [15:0] seq_counter;
reg [3:0] state_next;
reg [3:0] fault_next;
reg req_valid_next;
reg req_inflight_next;
reg fallback_next;
reg model_response_valid_seen_next;
reg request_stale_next;
reg geometry_invalid_next;
reg out_of_range_fault_next;
reg sequence_mismatch_fault_next;
reg service_unavailable_fault_next;
reg protocol_error_fault_next;
reg stale_response_fault_next;
reg [15:0] req_seq_next;
reg [15:0] last_accepted_seq_next;
reg [15:0] last_response_age_next;
reg [15:0] request_age_cycles_next;
reg [15:0] stale_reject_count_next;
reg [15:0] clamp_event_count_next;
reg [15:0] seq_counter_next;
reg active_fault;
reg geometry_match;
reg velocity_in_range;
reg setpoint_in_range;
reg timeout_active;
reg response_match;
reg response_service_unavailable;
reg response_protocol_error;
reg response_stale;
always @(*) begin
    state_next = current_state;
    fault_next = fault_code;
    req_valid_next = req_valid;
    req_inflight_next = req_inflight;
    fallback_next = fallback_active;
    model_response_valid_seen_next = model_response_valid_seen;
    request_stale_next = request_stale;
    geometry_invalid_next = geometry_invalid;
    out_of_range_fault_next = out_of_range_fault;
    sequence_mismatch_fault_next = sequence_mismatch_fault;
    service_unavailable_fault_next = service_unavailable_fault;
    protocol_error_fault_next = protocol_error_fault;
    stale_response_fault_next = stale_response_fault;
    req_seq_next = req_seq;
    last_accepted_seq_next = last_accepted_seq;
    last_response_age_next = last_response_age;
    request_age_cycles_next = request_age_cycles;
    stale_reject_count_next = stale_reject_count;
    clamp_event_count_next = clamp_event_count;
    seq_counter_next = seq_counter;
    active_fault = (fault_code != 4'd0);
    geometry_match = geom_valid & (geom_format_id_in == cfg_geometry_format_id) & (geom_source_id_in == cfg_geometry_source_id) & (geom_version_in == cfg_geometry_version);
    velocity_in_range = (stream_velocity_mps >= 16'd20) & (stream_velocity_mps <= 16'd55);
    setpoint_in_range = (cfg_stream_velocity_mps_setpoint >= 16'd20) & (cfg_stream_velocity_mps_setpoint <= 16'd55);
    timeout_active = req_inflight & (request_age_cycles >= cfg_command_timeout_cycles) & (cfg_command_timeout_cycles != 16'd0);
    response_match = rsp_valid & req_inflight & (rsp_seq == req_seq) & ~timeout_active;
    response_service_unavailable = rsp_valid & req_inflight & (rsp_seq == req_seq) & ~rsp_inference_status_not_executed & 1'b0;
    response_protocol_error = rsp_valid & req_inflight & (rsp_seq == req_seq) & rsp_inference_status_not_executed & 1'b0;
    response_stale = rsp_valid & req_inflight & (rsp_seq != req_seq);
    if (!rst_n) begin
        state_next = 4'd0;
        fault_next = 4'd0;
        req_valid_next = 1'b0;
        req_inflight_next = 1'b0;
        fallback_next = 1'b1;
        model_response_valid_seen_next = 1'b0;
        request_stale_next = 1'b0;
        geometry_invalid_next = 1'b0;
        out_of_range_fault_next = 1'b0;
        sequence_mismatch_fault_next = 1'b0;
        service_unavailable_fault_next = 1'b0;
        protocol_error_fault_next = 1'b0;
        stale_response_fault_next = 1'b0;
        req_seq_next = 16'd0;
        last_accepted_seq_next = 16'd0;
        last_response_age_next = 16'd0;
        request_age_cycles_next = 16'd0;
        stale_reject_count_next = 16'd0;
        clamp_event_count_next = 16'd0;
        seq_counter_next = 16'd0;
    end else begin
        if (cfg_clear_faults) begin
            fault_next = 4'd0;
            geometry_invalid_next = 1'b0;
            out_of_range_fault_next = 1'b0;
            sequence_mismatch_fault_next = 1'b0;
            service_unavailable_fault_next = 1'b0;
            protocol_error_fault_next = 1'b0;
            stale_response_fault_next = 1'b0;
        end
        if (tick_1ms | 1'b1) begin
            if (req_inflight_next) begin
                request_age_cycles_next = request_age_cycles + 16'd1;
            end else begin
                request_age_cycles_next = 16'd0;
            end
        end
        if (geometry_match == 1'b0) begin
            geometry_invalid_next = 1'b1;
            fault_next = 4'd4;
            fallback_next = 1'b1;
        end
        if ((velocity_in_range == 1'b0) | (setpoint_in_range == 1'b0)) begin
            out_of_range_fault_next = 1'b1;
            fault_next = 4'd1;
            fallback_next = 1'b1;
        end
        if (req_inflight_next == 1'b0) begin
            if (cfg_enable & geometry_match & velocity_in_range & setpoint_in_range & (fault_next == 4'd0)) begin
                req_valid_next = 1'b1;
                req_inflight_next = 1'b1;
                req_seq_next = seq_counter;
                seq_counter_next = seq_counter + 16'd1;
                request_age_cycles_next = 16'd0;
                state_next = 4'd1;
            end else begin
                req_valid_next = 1'b0;
                state_next = fallback_next ? 4'd0 : 4'd1;
            end
        end else begin
            req_valid_next = 1'b1;
            req_seq_next = seq_counter - 16'd1;
            if (req_ready) begin
                req_valid_next = 1'b0;
            end
            if (timeout_active) begin
                request_stale_next = 1'b1;
                stale_response_fault_next = 1'b1;
                fault_next = 4'd2;
                stale_reject_count_next = stale_reject_count + 16'd1;
                req_inflight_next = 1'b0;
                req_valid_next = 1'b0;
                fallback_next = 1'b1;
                last_response_age_next = request_age_cycles;
            end
            if (response_match) begin
                model_response_valid_seen_next = 1'b1;
                last_accepted_seq_next = rsp_seq;
                last_response_age_next = request_age_cycles;
                req_inflight_next = 1'b0;
                req_valid_next = 1'b0;
                state_next = 4'd2;
            end
            if (response_stale) begin
                sequence_mismatch_fault_next = 1'b1;
                fault_next = 4'd3;
                stale_reject_count_next = stale_reject_count + 16'd1;
                req_inflight_next = 1'b0;
                req_valid_next = 1'b0;
                fallback_next = 1'b1;
            end
            if (rsp_valid & req_inflight_next & rsp_inference_status_not_executed) begin
                protocol_error_fault_next = 1'b0;
                model_response_valid_seen_next = 1'b1;
            end
        end
        if (cfg_clear_faults) begin
            fallback_next = 1'b1;
        end
    end
end
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        current_state <= 4'd0;
        fault_code <= 4'd0;
        req_valid <= 1'b0;
        req_inflight <= 1'b0;
        fallback_active <= 1'b1;
        model_response_valid_seen <= 1'b0;
        request_stale <= 1'b0;
        geometry_invalid <= 1'b0;
        out_of_range_fault <= 1'b0;
        sequence_mismatch_fault <= 1'b0;
        service_unavailable_fault <= 1'b0;
        protocol_error_fault <= 1'b0;
        stale_response_fault <= 1'b0;
        req_seq <= 16'd0;
        last_accepted_seq <= 16'd0;
        last_response_age <= 16'd0;
        request_age_cycles <= 16'd0;
        stale_reject_count <= 16'd0;
        clamp_event_count <= 16'd0;
        seq_counter <= 16'd0;
    end else begin
        current_state <= state_next;
        fault_code <= fault_next;
        req_valid <= req_valid_next;
        req_inflight <= req_inflight_next;
        fallback_active <= fallback_next;
        model_response_valid_seen <= model_response_valid_seen_next;
        request_stale <= request_stale_next;
        geometry_invalid <= geometry_invalid_next;
        out_of_range_fault <= out_of_range_fault_next;
        sequence_mismatch_fault <= sequence_mismatch_fault_next;
        service_unavailable_fault <= service_unavailable_fault_next;
        protocol_error_fault <= protocol_error_fault_next;
        stale_response_fault <= stale_response_fault_next;
        req_seq <= req_seq_next;
        last_accepted_seq <= last_accepted_seq_next;
        last_response_age <= last_response_age_next;
        request_age_cycles <= request_age_cycles_next;
        stale_reject_count <= stale_reject_count_next;
        clamp_event_count <= clamp_event_count_next;
        seq_counter <= seq_counter_next;
    end
end
endmodule
