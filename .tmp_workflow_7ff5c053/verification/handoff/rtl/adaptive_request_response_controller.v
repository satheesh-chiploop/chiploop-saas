module adaptive_request_response_controller (
    clk,
    rst_n,
    cfg_enable,
    operating_velocity_mps,
    response_timeout_cycles,
    request_age_limit_cycles,
    actuator_min_limit,
    actuator_max_limit,
    safe_fallback_setpoint,
    mode_select,
    geometry_ref_id,
    config_error,
    cmd_rsp_ready,
    cmd_rsp_valid,
    cmd_rsp_data,
    resp_valid,
    resp_data,
    resp_ready,
    actuator_out,
    status_out,
    transaction_id_echo,
    busy,
    request_pending,
    response_valid,
    stale_reject,
    timeout_fault,
    clamp_active,
    fallback_active
);
    input clk;
    input rst_n;
    input cfg_enable;
    input [15:0] operating_velocity_mps;
    input [15:0] response_timeout_cycles;
    input [15:0] request_age_limit_cycles;
    input [15:0] actuator_min_limit;
    input [15:0] actuator_max_limit;
    input [15:0] safe_fallback_setpoint;
    input [3:0] mode_select;
    input [7:0] geometry_ref_id;
    input config_error;
    input cmd_rsp_ready;
    output cmd_rsp_valid;
    output [127:0] cmd_rsp_data;
    input resp_valid;
    input [127:0] resp_data;
    output resp_ready;
    output [15:0] actuator_out;
    output [15:0] status_out;
    output [15:0] transaction_id_echo;
    output busy;
    output request_pending;
    output response_valid;
    output stale_reject;
    output timeout_fault;
    output clamp_active;
    output fallback_active;

    reg cmd_rsp_valid_r;
    reg [127:0] cmd_rsp_data_r;
    reg resp_ready_r;
    reg [15:0] actuator_out_r;
    reg [15:0] status_out_r;
    reg [15:0] transaction_id_echo_r;
    reg busy_r;
    reg request_pending_r;
    reg response_valid_r;
    reg stale_reject_r;
    reg timeout_fault_r;
    reg clamp_active_r;
    reg fallback_active_r;
    reg [15:0] transaction_id_r;
    reg [15:0] age_counter_r;
    reg [15:0] timeout_counter_r;

    assign cmd_rsp_valid = cmd_rsp_valid_r;
    assign cmd_rsp_data = cmd_rsp_data_r;
    assign resp_ready = resp_ready_r;
    assign actuator_out = actuator_out_r;
    assign status_out = status_out_r;
    assign transaction_id_echo = transaction_id_echo_r;
    assign busy = busy_r;
    assign request_pending = request_pending_r;
    assign response_valid = response_valid_r;
    assign stale_reject = stale_reject_r;
    assign timeout_fault = timeout_fault_r;
    assign clamp_active = clamp_active_r;
    assign fallback_active = fallback_active_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cmd_rsp_valid_r <= 1'b0;
            cmd_rsp_data_r <= 128'h00000000000000000000000000000000;
            resp_ready_r <= 1'b1;
            actuator_out_r <= 16'd0;
            status_out_r <= 16'd0;
            transaction_id_echo_r <= 16'd0;
            busy_r <= 1'b0;
            request_pending_r <= 1'b0;
            response_valid_r <= 1'b0;
            stale_reject_r <= 1'b0;
            timeout_fault_r <= 1'b0;
            clamp_active_r <= 1'b0;
            fallback_active_r <= 1'b1;
            transaction_id_r <= 16'd0;
            age_counter_r <= 16'd0;
            timeout_counter_r <= 16'd0;
        end else begin
            cmd_rsp_valid_r <= 1'b0;
            response_valid_r <= 1'b0;
            stale_reject_r <= 1'b0;
            clamp_active_r <= 1'b0;
            timeout_counter_r <= timeout_counter_r + 16'd1;

            if (!cfg_enable || config_error) begin
                fallback_active_r <= 1'b1;
                busy_r <= 1'b0;
                request_pending_r <= 1'b0;
                cmd_rsp_valid_r <= 1'b0;
                resp_ready_r <= 1'b1;
                actuator_out_r <= safe_fallback_setpoint;
            end else begin
                fallback_active_r <= 1'b0;
                resp_ready_r <= 1'b1;
                if (!request_pending_r && !cmd_rsp_valid_r) begin
                    cmd_rsp_valid_r <= 1'b1;
                    transaction_id_r <= transaction_id_r + 16'd1;
                    transaction_id_echo_r <= transaction_id_r + 16'd1;
                    busy_r <= 1'b1;
                    request_pending_r <= 1'b1;
                    age_counter_r <= 16'd0;
                    timeout_counter_r <= 16'd0;
                    cmd_rsp_data_r <= {8'hA5, transaction_id_r + 16'd1, operating_velocity_mps, 8'h00, geometry_ref_id, response_timeout_cycles, {8'h00, mode_select, 4'h0, 4'h0}, 32'h00000000};
                end else if (request_pending_r) begin
                    age_counter_r <= age_counter_r + 16'd1;
                    if (resp_valid) begin
                        if (resp_data[127:120] == 8'h5A && resp_data[119:104] == transaction_id_echo_r && resp_data[103] == 1'b1) begin
                            response_valid_r <= 1'b1;
                            request_pending_r <= 1'b0;
                            busy_r <= 1'b0;
                            fallback_active_r <= 1'b0;
                            if (resp_data[15:0] < actuator_min_limit) begin
                                actuator_out_r <= actuator_min_limit;
                                clamp_active_r <= 1'b1;
                            end else if (resp_data[15:0] > actuator_max_limit) begin
                                actuator_out_r <= actuator_max_limit;
                                clamp_active_r <= 1'b1;
                            end else begin
                                actuator_out_r <= resp_data[15:0];
                            end
                        end else begin
                            stale_reject_r <= 1'b1;
                            fallback_active_r <= 1'b1;
                            request_pending_r <= 1'b0;
                            busy_r <= 1'b0;
                            actuator_out_r <= safe_fallback_setpoint;
                        end
                    end else if (timeout_counter_r >= response_timeout_cycles) begin
                        timeout_fault_r <= 1'b1;
                        fallback_active_r <= 1'b1;
                        request_pending_r <= 1'b0;
                        busy_r <= 1'b0;
                        actuator_out_r <= safe_fallback_setpoint;
                    end else begin
                        busy_r <= 1'b1;
                        actuator_out_r <= safe_fallback_setpoint;
                    end
                end else begin
                    busy_r <= 1'b0;
                    actuator_out_r <= safe_fallback_setpoint;
                end
            end

            status_out_r <= {transaction_id_echo_r[7:0], fallback_active_r, clamp_active_r, timeout_fault_r, stale_reject_r, response_valid_r, request_pending_r, busy_r, config_error};
        end
    end
endmodule
