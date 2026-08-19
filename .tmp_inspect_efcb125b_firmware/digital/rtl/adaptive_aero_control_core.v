module adaptive_aero_control_core (
    input             clk,
    input             reset_n,
    input      [1:0] cfg_mode,
    input             cfg_cmd_valid,
    input      [15:0] cfg_velocity_q8_8,
    input      [15:0] cfg_geometry_handle,
    input      [15:0] cfg_request_seq,
    input      [15:0] cfg_timeout_threshold,
    input      [15:0] cfg_actuator_min,
    input      [15:0] cfg_actuator_max,
    input      [15:0] cfg_actuator_slew,
    input      [15:0] cfg_velocity_low_limit,
    input      [15:0] cfg_velocity_high_limit,
    input      [15:0] cfg_safe_state_cmd,
    input             cfg_hold_last_safe,
    input      [7:0] cfg_irq_enable,
    input             cfg_fault_clear,
    input             cfg_irq_ack,
    input             req_ready_i,
    output reg        req_valid_o,
    output reg [63:0] req_data_o,
    input             resp_valid_i,
    output reg        resp_ready_o,
    input      [63:0] resp_data_i,
    output reg        status_outstanding_req,
    output reg [15:0] status_last_accepted_seq,
    output reg [15:0] status_response_seq,
    output reg [15:0] status_timeout_count,
    output reg [15:0] status_stale_reject_count,
    output reg [15:0] status_invalid_env_count,
    output reg [7:0] status_fault_code,
    output reg        status_safe_state,
    output reg        status_fault_latched,
    output reg [7:0] status_irq_sticky,
    output reg [15:0] status_actuator_cmd,
    output reg        status_actuator_valid,
    output reg [15:0] status_age_counter,
    output reg [63:0] status_last_req_word,
    output reg [63:0] status_last_resp_word,
    output reg [15:0] actuator_cmd_o,
    output reg        actuator_valid_o,
    output reg        fault_o,
    output reg        safe_state_o,
    output reg        irq_o
);
    localparam [7:0] FAULT_NONE = 8'h00;
    localparam [7:0] FAULT_TIMEOUT = 8'h01;
    localparam [7:0] FAULT_STALE = 8'h02;
    localparam [7:0] FAULT_INVALID_ENV = 8'h03;
    localparam [7:0] FAULT_RESP_INVALID = 8'h04;

    reg [15:0] current_cmd;
    reg [15:0] next_cmd;
    reg [15:0] safe_cmd_hold;
    reg [15:0] req_seq_next;
    reg [63:0] req_word_next;
    reg [15:0] age_next;
    reg [15:0] timeout_next;
    reg [15:0] stale_next;
    reg [15:0] invalid_env_next;
    reg [7:0]  fault_code_next;
    reg [7:0]  irq_sticky_next;
    reg        outstanding_next;
    reg        safe_state_next;
    reg        fault_latched_next;
    reg        actuator_valid_next;
    reg        fault_next;
    reg        irq_next;
    reg        response_accept;
    reg        env_ok;
    reg        timeout_hit;
    reg        stale_hit;
    reg        response_ok;
    reg [15:0] clamp_min;
    reg [15:0] clamp_max;
    reg [15:0] slew_limit;
    reg [15:0] vel_lo;
    reg [15:0] vel_hi;
    reg [15:0] vraw;
    reg [15:0] req_seq_use;
    reg [63:0] decoded_resp;
    reg [15:0] resp_seq;
    reg [15:0] resp_cmd;
    reg [15:0] clamped_cmd;
    reg [15:0] slew_cmd;
    reg [15:0] delta_abs;

    always @(*) begin
        req_seq_use = cfg_request_seq;
        vel_lo = cfg_velocity_low_limit;
        vel_hi = cfg_velocity_high_limit;
        vraw = cfg_velocity_q8_8;
        env_ok = (vraw >= vel_lo) && (vraw <= vel_hi);
        clamp_min = (cfg_actuator_min <= cfg_actuator_max) ? cfg_actuator_min : cfg_actuator_max;
        clamp_max = (cfg_actuator_min <= cfg_actuator_max) ? cfg_actuator_max : cfg_actuator_min;
        slew_limit = cfg_actuator_slew;
        safe_cmd_hold = status_actuator_cmd;
        decoded_resp = resp_data_i;
        resp_seq = decoded_resp[63:48];
        resp_cmd = decoded_resp[15:0];
        timeout_hit = status_outstanding_req && (cfg_timeout_threshold != 16'd0) && (status_age_counter >= cfg_timeout_threshold);
        stale_hit = resp_valid_i && (!status_outstanding_req || (resp_seq != status_last_accepted_seq));
        response_ok = resp_valid_i && status_outstanding_req && (resp_seq == status_last_accepted_seq) && decoded_resp[47];
        response_accept = response_ok && !status_fault_latched && env_ok;
        req_word_next = {cfg_mode, 2'b00, req_seq_use, cfg_geometry_handle, cfg_velocity_q8_8, 16'hA55A};
        req_valid_o = 1'b0;
        resp_ready_o = 1'b1;
        next_cmd = current_cmd;
        clamped_cmd = resp_cmd;
        if (clamped_cmd < clamp_min) clamped_cmd = clamp_min;
        if (clamped_cmd > clamp_max) clamped_cmd = clamp_max;
        slew_cmd = clamped_cmd;
        if (slew_cmd > current_cmd) begin
            delta_abs = slew_cmd - current_cmd;
            if (delta_abs > slew_limit) slew_cmd = current_cmd + slew_limit;
        end else begin
            delta_abs = current_cmd - slew_cmd;
            if (delta_abs > slew_limit) slew_cmd = current_cmd - slew_limit;
        end
        if (cfg_cmd_valid && !status_outstanding_req && !status_fault_latched) begin
            req_valid_o = 1'b1;
        end
        if (response_accept) begin
            next_cmd = slew_cmd;
        end
        if (status_fault_latched) begin
            if (cfg_hold_last_safe) next_cmd = status_actuator_cmd;
            else next_cmd = cfg_safe_state_cmd;
        end
        if (!env_ok) begin
            next_cmd = cfg_safe_state_cmd;
        end
        if (timeout_hit) begin
            next_cmd = cfg_safe_state_cmd;
        end
        if (stale_hit) begin
            next_cmd = cfg_safe_state_cmd;
        end
        if (resp_valid_i && status_outstanding_req && !decoded_resp[47]) begin
            next_cmd = cfg_safe_state_cmd;
        end
        req_valid_o = req_valid_o && req_ready_i;
        req_data_o = req_word_next;
    end

    always @(posedge clk) begin
        if (!reset_n) begin
            status_outstanding_req <= 1'b0;
            status_last_accepted_seq <= 16'd0;
            status_response_seq <= 16'd0;
            status_timeout_count <= 16'd0;
            status_stale_reject_count <= 16'd0;
            status_invalid_env_count <= 16'd0;
            status_fault_code <= FAULT_NONE;
            status_safe_state <= 1'b1;
            status_fault_latched <= 1'b0;
            status_irq_sticky <= 8'd0;
            status_actuator_cmd <= 16'd0;
            status_actuator_valid <= 1'b0;
            status_age_counter <= 16'd0;
            status_last_req_word <= 64'd0;
            status_last_resp_word <= 64'd0;
            actuator_cmd_o <= 16'd0;
            actuator_valid_o <= 1'b0;
            fault_o <= 1'b0;
            safe_state_o <= 1'b1;
            irq_o <= 1'b0;
            current_cmd <= 16'd0;
        end else begin
            if (cfg_cmd_valid && !status_outstanding_req && !status_fault_latched) begin
                status_outstanding_req <= 1'b1;
                status_last_accepted_seq <= cfg_request_seq;
                status_age_counter <= 16'd0;
                status_last_req_word <= {cfg_mode, 2'b00, cfg_request_seq, cfg_geometry_handle, cfg_velocity_q8_8, 16'hA55A};
            end else if (status_outstanding_req) begin
                status_age_counter <= status_age_counter + 16'd1;
            end
            if (resp_valid_i && status_outstanding_req) begin
                status_last_resp_word <= resp_data_i;
                if (resp_data_i[63:48] == status_last_accepted_seq && resp_data_i[47]) begin
                    status_response_seq <= resp_data_i[63:48];
                    status_outstanding_req <= 1'b0;
                    status_age_counter <= 16'd0;
                    status_actuator_cmd <= status_actuator_cmd;
                    status_actuator_valid <= env_ok;
                    current_cmd <= status_actuator_cmd;
                    status_irq_sticky[0] <= 1'b1;
                end else begin
                    status_stale_reject_count <= status_stale_reject_count + 16'd1;
                    status_irq_sticky[2] <= 1'b1;
                end
            end else if (resp_valid_i && !status_outstanding_req) begin
                status_stale_reject_count <= status_stale_reject_count + 16'd1;
                status_irq_sticky[2] <= 1'b1;
            end
            if (!env_ok) begin
                status_invalid_env_count <= status_invalid_env_count + 16'd1;
                status_fault_latched <= 1'b1;
                status_fault_code <= FAULT_INVALID_ENV;
                status_irq_sticky[3] <= 1'b1;
            end
            if (status_outstanding_req && (cfg_timeout_threshold != 16'd0) && (status_age_counter >= cfg_timeout_threshold)) begin
                status_timeout_count <= status_timeout_count + 16'd1;
                status_fault_latched <= 1'b1;
                status_fault_code <= FAULT_TIMEOUT;
                status_outstanding_req <= 1'b0;
                status_irq_sticky[1] <= 1'b1;
            end
            if (cfg_fault_clear && !status_outstanding_req) begin
                status_fault_latched <= 1'b0;
                status_fault_code <= FAULT_NONE;
                status_irq_sticky[4] <= 1'b1;
                if (cfg_hold_last_safe) status_safe_state <= 1'b1;
            end
            if (cfg_irq_ack) begin
                status_irq_sticky <= 8'd0;
            end
            if (status_fault_latched) begin
                status_safe_state <= 1'b1;
                if (cfg_hold_last_safe) status_actuator_cmd <= status_actuator_cmd;
                else status_actuator_cmd <= cfg_safe_state_cmd;
                status_actuator_valid <= 1'b0;
            end else if (env_ok && !status_outstanding_req && !resp_valid_i) begin
                status_safe_state <= 1'b0;
                status_actuator_valid <= 1'b1;
            end
            if (!status_fault_latched && response_ok && env_ok) begin
                status_actuator_cmd <= current_cmd;
                status_actuator_valid <= 1'b1;
                status_safe_state <= 1'b0;
            end
            actuator_cmd_o <= status_actuator_cmd;
            actuator_valid_o <= status_actuator_valid;
            fault_o <= status_fault_latched;
            safe_state_o <= status_safe_state;
            irq_o <= |(status_irq_sticky & cfg_irq_enable);
        end
    end
endmodule
