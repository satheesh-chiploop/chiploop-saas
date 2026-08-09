module pwm_fpga_demo (
    input  clk,
    output led
);

reg [7:0] pwm_counter;
reg [7:0] duty_cycle;
reg       direction;
reg [15:0] slow_counter;

wire pwm_led;

assign led = pwm_led;
assign pwm_led = (pwm_counter < duty_cycle);

always @(posedge clk) begin
    pwm_counter <= pwm_counter + 8'h01;

    if (slow_counter == 16'hC350) begin
        slow_counter <= 16'h0000;

        if (direction) begin
            if (duty_cycle == 8'hFF) begin
                duty_cycle <= 8'hFF;
                direction <= 1'b0;
            end else begin
                duty_cycle <= duty_cycle + 8'h01;
            end
        end else begin
            if (duty_cycle == 8'h00) begin
                duty_cycle <= 8'h00;
                direction <= 1'b1;
            end else begin
                duty_cycle <= duty_cycle - 8'h01;
            end
        end
    end else begin
        slow_counter <= slow_counter + 16'h0001;
    end
end

initial begin
    pwm_counter = 8'h00;
    duty_cycle   = 8'h00;
    direction    = 1'b1;
    slow_counter = 16'h0000;
end

endmodule
