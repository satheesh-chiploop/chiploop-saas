module command_conditioner (
    input clk,
    input rst_n,
    input [1:0] status_mode,
    input fault_latched,
    input timeout_status,
    input stale_status,
    input active,
    input wait_response,
    input rsp_cmd_valid,
    input [15:0] rsp_act_cmd,
    input [15:0] cfg_act_min,
    input [15:0] cfg_act_max,
    input [7:0] cfg_rate_limit,
    input [15:0] cfg_safe_output,
    output reg [1:0] status_mode_seen,
    output reg act_cmd_valid,
    output reg [15:0] act_cmd,
    output reg act_cmd_hold,
    output reg [15:0] last_cmd
);

reg [15:0] clamped_cmd;
reg [15:0] rate_limited_cmd;
reg [16:0] delta_abs;
reg [15:0] prev_cmd;
reg [15:0] fallback_cmd;

always @(*) begin
    clamped_cmd = rsp_act_cmd;
    if (clamped_cmd < cfg_act_min)
        clamped_cmd = cfg_act_min;
    if (clamped_cmd > cfg_act_max)
        clamped_cmd = cfg_act_max;
    delta_abs = (clamped_cmd >= prev_cmd) ? ({1'b0, clamped_cmd} - {1'b0, prev_cmd}) : ({1'b0, prev_cmd} - {1'b0, clamped_cmd});
    if (delta_abs[15:0] > {8'b0, cfg_rate_limit}) begin
        if (clamped_cmd >= prev_cmd)
            rate_limited_cmd = prev_cmd + {8'b0, cfg_rate_limit};
        else
            rate_limited_cmd = prev_cmd - {8'b0, cfg_rate_limit};
    end else begin
        rate_limited_cmd = clamped_cmd;
    end
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        status_mode_seen <= 2'b00;
        act_cmd_valid <= 1'b0;
        act_cmd <= 16'h0000;
        act_cmd_hold <= 1'b1;
        last_cmd <= 16'h0000;
        prev_cmd <= 16'h0000;
        fallback_cmd <= 16'h0000;
    end else begin
        status_mode_seen <= status_mode;
        act_cmd_hold <= 1'b1;
        if (fault_latched || timeout_status || stale_status || !active || wait_response || !rsp_cmd_valid) begin
            act_cmd_valid <= 1'b0;
            act_cmd <= fallback_cmd;
        end else begin
            act_cmd_valid <= 1'b1;
            act_cmd <= rate_limited_cmd;
            last_cmd <= rate_limited_cmd;
            prev_cmd <= rate_limited_cmd;
            act_cmd_hold <= 1'b0;
            fallback_cmd <= cfg_safe_output;
        end
        if (fault_latched || timeout_status || stale_status) begin
            act_cmd <= fallback_cmd;
            fallback_cmd <= cfg_safe_output;
        end
    end
end

endmodule
