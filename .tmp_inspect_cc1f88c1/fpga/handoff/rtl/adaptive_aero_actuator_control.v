module adaptive_aero_actuator_control (
    clk,
    reset_n,
    cfg_global_enable,
    cfg_release_enable,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_actuator_rate_limit,
    accepted_response_summary,
    response_ready,
    busy,
    stale_rejected,
    timeout_fault,
    invalid_response,
    sequence_mismatch,
    fault_event_pulse,
    actuator_cmd_valid,
    actuator_cmd_ready,
    actuator_cmd_data,
    last_accepted_command,
    clamp_applied,
    fallback_active
);
    input clk;
    input reset_n;
    input cfg_global_enable;
    input cfg_release_enable;
    input [15:0] cfg_actuator_min_limit;
    input [15:0] cfg_actuator_max_limit;
    input [15:0] cfg_actuator_rate_limit;
    input [63:0] accepted_response_summary;
    input response_ready;
    input busy;
    input stale_rejected;
    input timeout_fault;
    input invalid_response;
    input sequence_mismatch;
    input fault_event_pulse;
    input actuator_cmd_ready;
    output actuator_cmd_valid;
    output [31:0] actuator_cmd_data;
    output [31:0] last_accepted_command;
    output clamp_applied;
    output fallback_active;

    reg actuator_cmd_valid_r;
    reg [31:0] actuator_cmd_data_r;
    reg [31:0] last_accepted_command_r;
    reg clamp_applied_r;
    reg fallback_active_r;
    reg [31:0] prev_cmd;
    reg [31:0] raw_cmd;
    reg [31:0] sat_cmd;
    reg [31:0] rate_cmd;
    reg [31:0] min_cmd;
    reg [31:0] max_cmd;
    reg [31:0] rate_lim;
    reg [31:0] delta;

    assign actuator_cmd_valid = actuator_cmd_valid_r;
    assign actuator_cmd_data = actuator_cmd_data_r;
    assign last_accepted_command = last_accepted_command_r;
    assign clamp_applied = clamp_applied_r;
    assign fallback_active = fallback_active_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            actuator_cmd_valid_r <= 1'b0;
            actuator_cmd_data_r <= 32'h00000000;
            last_accepted_command_r <= 32'h00000000;
            clamp_applied_r <= 1'b0;
            fallback_active_r <= 1'b1;
            prev_cmd <= 32'h00000000;
            raw_cmd <= 32'h00000000;
            sat_cmd <= 32'h00000000;
            rate_cmd <= 32'h00000000;
            min_cmd <= 32'h00000000;
            max_cmd <= 32'h00000000;
            rate_lim <= 32'h00000000;
            delta <= 32'h00000000;
        end else begin
            clamp_applied_r <= 1'b0;
            fallback_active_r <= 1'b1;
            actuator_cmd_valid_r <= 1'b0;
            if (cfg_global_enable && cfg_release_enable && response_ready && !busy && !stale_rejected && !timeout_fault && !invalid_response && !sequence_mismatch) begin
                raw_cmd <= accepted_response_summary[31:0];
                min_cmd <= {16'h0000, cfg_actuator_min_limit};
                max_cmd <= {16'h0000, cfg_actuator_max_limit};
                rate_lim <= {16'h0000, cfg_actuator_rate_limit};
                if (accepted_response_summary[31:0] < {16'h0000, cfg_actuator_min_limit}) begin
                    sat_cmd <= {16'h0000, cfg_actuator_min_limit};
                    clamp_applied_r <= 1'b1;
                end else if (accepted_response_summary[31:0] > {16'h0000, cfg_actuator_max_limit}) begin
                    sat_cmd <= {16'h0000, cfg_actuator_max_limit};
                    clamp_applied_r <= 1'b1;
                end else begin
                    sat_cmd <= accepted_response_summary[31:0];
                end
                if (cfg_actuator_rate_limit != 16'h0000) begin
                    if ((accepted_response_summary[31:0] > prev_cmd) && ((accepted_response_summary[31:0] - prev_cmd) > {16'h0000, cfg_actuator_rate_limit})) begin
                        rate_cmd <= prev_cmd + {16'h0000, cfg_actuator_rate_limit};
                        clamp_applied_r <= 1'b1;
                    end else if ((prev_cmd > accepted_response_summary[31:0]) && ((prev_cmd - accepted_response_summary[31:0]) > {16'h0000, cfg_actuator_rate_limit})) begin
                        rate_cmd <= prev_cmd - {16'h0000, cfg_actuator_rate_limit};
                        clamp_applied_r <= 1'b1;
                    end else begin
                        rate_cmd <= sat_cmd;
                    end
                end else begin
                    rate_cmd <= sat_cmd;
                end
                actuator_cmd_data_r <= rate_cmd;
                if (actuator_cmd_ready) begin
                    actuator_cmd_valid_r <= 1'b1;
                    last_accepted_command_r <= rate_cmd;
                    prev_cmd <= rate_cmd;
                    fallback_active_r <= 1'b0;
                end
            end
            if (fault_event_pulse || stale_rejected || timeout_fault || invalid_response || sequence_mismatch) begin
                fallback_active_r <= 1'b1;
                actuator_cmd_valid_r <= 1'b0;
            end
        end
    end
endmodule
