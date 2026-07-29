module pwm_fpga_demo (
    clk,
    led
);

input clk;
output led;

reg [7:0] pwm_cnt;
reg [7:0] duty_cycle;
reg       direction;
reg [15:0] slow_cnt;

assign led = (pwm_cnt < duty_cycle);

always @(posedge clk) begin
    pwm_cnt <= pwm_cnt + 8'h01;

    slow_cnt <= slow_cnt + 16'h0001;

    if (slow_cnt == 16'hFFFF) begin
        if (direction) begin
            if (duty_cycle == 8'hF0) begin
                direction <= 1'b0;
                duty_cycle <= duty_cycle - 8'h01;
            end else begin
                duty_cycle <= duty_cycle + 8'h01;
            end
        end else begin
            if (duty_cycle == 8'h10) begin
                direction <= 1'b1;
                duty_cycle <= duty_cycle + 8'h01;
            end else begin
                duty_cycle <= duty_cycle - 8'h01;
            end
        end
    end
end

initial begin
    pwm_cnt = 8'h00;
    duty_cycle = 8'h10;
    direction = 1'b1;
    slow_cnt = 16'h0000;
end

endmodule
