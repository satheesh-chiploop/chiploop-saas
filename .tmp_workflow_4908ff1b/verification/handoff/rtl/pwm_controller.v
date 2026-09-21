module pwm_controller (
    clk,
    reset_n,
    enable,
    duty_cycle,
    period,
    pwm_out,
    counter_value
);

input clk;
input reset_n;
input enable;
input [7:0] duty_cycle;
input [7:0] period;
output pwm_out;
output [7:0] counter_value;
reg [7:0] counter_r;
assign counter_value = counter_r;
assign pwm_out = (counter_r < duty_cycle) ? 1'b1 : 1'b0;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        counter_r <= 8'h00;
    end else if (enable) begin
        if (counter_r == period) begin
            counter_r <= 8'h00;
        end else begin
            counter_r <= counter_r + 8'h01;
        end
    end
end

endmodule
