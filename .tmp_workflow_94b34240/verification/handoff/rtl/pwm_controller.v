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
reg pwm_out_r;

assign counter_value = counter_r;
assign pwm_out = pwm_out_r;

always @(posedge clk) begin
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

always @(*) begin
    if (!reset_n) begin
        pwm_out_r = 1'b0;
    end else begin
        pwm_out_r = (counter_r < duty_cycle);
    end
end

endmodule
