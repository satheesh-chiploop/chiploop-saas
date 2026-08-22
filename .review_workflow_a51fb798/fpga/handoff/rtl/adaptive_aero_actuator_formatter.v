module adaptive_aero_actuator_formatter (
    clk,
    reset_n,
    cfg_clamp_min,
    cfg_clamp_max,
    cfg_mode_status,
    cfg_operating_velocity_mps,
    rsp_valid_result,
    rsp_packet_128,
    act_cmd_pos,
    act_cmd_rate,
    act_cmd_enable,
    act_cmd_valid,
    act_cmd_fault_latched,
    fallback_active,
    fault_timeout_sticky,
    fault_stale_sticky,
    fault_invalid_sticky,
    fault_queue_full_sticky,
    fault_host_not_ready_sticky
);
    input clk;
    input reset_n;
    input [15:0] cfg_clamp_min;
    input [15:0] cfg_clamp_max;
    input [7:0] cfg_mode_status;
    input [15:0] cfg_operating_velocity_mps;
    input rsp_valid_result;
    input [127:0] rsp_packet_128;
    output reg [15:0] act_cmd_pos;
    output reg [11:0] act_cmd_rate;
    output reg act_cmd_enable;
    output reg act_cmd_valid;
    output reg act_cmd_fault_latched;
    output reg fallback_active;
    input fault_timeout_sticky;
    input fault_stale_sticky;
    input fault_invalid_sticky;
    input fault_queue_full_sticky;
    input fault_host_not_ready_sticky;

    reg [15:0] pos_calc;
    reg [11:0] rate_calc;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            act_cmd_pos <= 16'h0000;
            act_cmd_rate <= 12'h000;
            act_cmd_enable <= 1'b0;
            act_cmd_valid <= 1'b0;
            act_cmd_fault_latched <= 1'b0;
            fallback_active <= 1'b0;
            pos_calc <= 16'h0000;
            rate_calc <= 12'h000;
        end else begin
            act_cmd_valid <= 1'b0;
            act_cmd_enable <= 1'b0;
            if (fault_timeout_sticky | fault_stale_sticky | fault_invalid_sticky | fault_queue_full_sticky | fault_host_not_ready_sticky) begin
                act_cmd_fault_latched <= 1'b1;
                fallback_active <= 1'b1;
                act_cmd_pos <= cfg_clamp_min;
                act_cmd_rate <= 12'h000;
            end else if (rsp_valid_result) begin
                pos_calc <= rsp_packet_128[15:0] + cfg_operating_velocity_mps;
                if (pos_calc < cfg_clamp_min) act_cmd_pos <= cfg_clamp_min;
                else if (pos_calc > cfg_clamp_max) act_cmd_pos <= cfg_clamp_max;
                else act_cmd_pos <= pos_calc;
                rate_calc <= rsp_packet_128[27:16];
                act_cmd_rate <= rate_calc;
                act_cmd_enable <= 1'b1;
                act_cmd_valid <= 1'b1;
                act_cmd_fault_latched <= 1'b0;
                fallback_active <= 1'b0;
            end
        end
    end
endmodule
