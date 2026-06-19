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

reg [7:0] counter_reg;
reg pwm_reg;

assign counter_value = counter_reg;
assign pwm_out = pwm_reg;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        counter_reg <= 8'h00;
        pwm_reg <= 1'b0;
    end else begin
        if (enable) begin
            if (counter_reg == period) begin
                counter_reg <= 8'h00;
            end else begin
                counter_reg <= counter_reg + 8'h01;
            end
        end else begin
            counter_reg <= counter_reg;
        end

        if (counter_reg < duty_cycle) begin
            pwm_reg <= 1'b1;
        end else begin
            pwm_reg <= 1'b0;
        end
    end
end

endmodule
