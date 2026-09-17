module pwm_controller (
    input clk,
    input reset_n,
    input enable,
    input [7:0] duty_cycle,
    input [7:0] period,
    output reg pwm_out,
    output reg [7:0] counter_value
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        counter_value <= 8'h00;
        pwm_out <= 1'b0;
    end else begin
        if (enable) begin
            if (counter_value == period) begin
                counter_value <= 8'h00;
            end else begin
                counter_value <= counter_value + 8'h01;
            end
        end
        pwm_out <= (counter_value < duty_cycle);
    end
end

endmodule
