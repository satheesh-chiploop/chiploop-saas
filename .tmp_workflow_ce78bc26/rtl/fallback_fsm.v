module fallback_fsm (
    clk,
    reset_n,
    safe_mode,
    fallback_setpoint_a,
    fallback_setpoint_b,
    fallback_setpoint_c,
    fallback_setpoint_d,
    fallback_output,
    fallback_valid,
    fallback_active
);
input clk;
input reset_n;
input safe_mode;
input [15:0] fallback_setpoint_a;
input [15:0] fallback_setpoint_b;
input [15:0] fallback_setpoint_c;
input [15:0] fallback_setpoint_d;
output [63:0] fallback_output;
output fallback_valid;
output fallback_active;

reg [63:0] fallback_output_r;
reg fallback_valid_r;
reg fallback_active_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        fallback_output_r <= 64'h0000000000000000;
        fallback_valid_r <= 1'b0;
        fallback_active_r <= 1'b1;
    end else begin
        fallback_active_r <= safe_mode;
        fallback_valid_r <= safe_mode;
        if (safe_mode) begin
            fallback_output_r <= {fallback_setpoint_d, fallback_setpoint_c, fallback_setpoint_b, fallback_setpoint_a};
        end
    end
end

assign fallback_output = fallback_output_r;
assign fallback_valid = fallback_valid_r;
assign fallback_active = fallback_active_r;

endmodule
