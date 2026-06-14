module pwm_controller (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    rd_data,
    pwm_out,
    counter_value
);
input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [7:0] wr_data;
input rd_en;
input [7:0] rd_addr;
output [7:0] rd_data;
output pwm_out;
output [7:0] counter_value;

wire enable;
wire [7:0] duty_cycle;
wire [7:0] period;
wire [7:0] regs_counter_value;

assign counter_value = regs_counter_value;
assign pwm_out = enable & (regs_counter_value < duty_cycle);

pwm_controller_regs u_pwm_controller_regs (
    .clk(clk),
    .reset_n(reset_n),
    .wr_en(wr_en),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_addr(rd_addr),
    .rd_data(rd_data),
    .enable(enable),
    .duty_cycle(duty_cycle),
    .period(period),
    .counter_value(regs_counter_value)
);

endmodule
