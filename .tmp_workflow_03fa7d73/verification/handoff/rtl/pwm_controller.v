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
    wire [7:0] period_eff;
    wire pwm_out_int;

    assign period_eff = period;
    assign counter_value = counter_reg;
    assign pwm_out = pwm_out_int;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            counter_reg <= 8'h00;
        end else if (enable) begin
            if (period_eff == 8'h00) begin
                counter_reg <= 8'h00;
            end else if (counter_reg >= period_eff) begin
                counter_reg <= 8'h00;
            end else begin
                counter_reg <= counter_reg + 8'h01;
            end
        end
    end

    assign pwm_out_int = (reset_n && (counter_reg < duty_cycle)) ? 1'b1 : 1'b0;

endmodule
