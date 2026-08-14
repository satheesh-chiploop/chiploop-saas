module adaptive_aero_control_top (
    input        clk,
    input        reset_n,
    input  [15:0] safe_cmd_value,
    input  [1:0] safe_cmd_mode,
    input         safe_cmd_valid,
    output reg    act_cmd_valid,
    output reg    act_cmd_enable,
    output reg [15:0] act_cmd_value,
    output reg [1:0] act_cmd_mode
);

reg [15:0] cmd_value_r;
reg [1:0]  cmd_mode_r;
reg        cmd_valid_r;
reg        cmd_enable_r;

reg [15:0] safe_value_r;
reg [1:0]  safe_mode_r;
reg        safe_valid_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cmd_value_r  <= 16'h0000;
        cmd_mode_r   <= 2'b00;
        cmd_valid_r  <= 1'b0;
        cmd_enable_r <= 1'b0;
        safe_value_r  <= 16'h0000;
        safe_mode_r   <= 2'b00;
        safe_valid_r  <= 1'b0;
    end else begin
        safe_value_r <= safe_cmd_value;
        safe_mode_r  <= safe_cmd_mode;
        safe_valid_r <= safe_cmd_valid;

        cmd_value_r  <= safe_cmd_value;
        cmd_mode_r   <= safe_cmd_mode;
        cmd_valid_r  <= safe_cmd_valid;
        cmd_enable_r <= safe_cmd_valid;
    end
end

always @(*) begin
    act_cmd_valid  = cmd_valid_r & safe_valid_r;
    act_cmd_enable = cmd_enable_r & safe_valid_r;
    act_cmd_value  = (safe_valid_r) ? cmd_value_r : safe_value_r;
    act_cmd_mode   = (safe_valid_r) ? cmd_mode_r  : safe_mode_r;
end

endmodule
