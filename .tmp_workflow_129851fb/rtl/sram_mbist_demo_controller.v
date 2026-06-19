module sram_mbist_demo_controller (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    bist_start,
    rd_data,
    ready,
    bist_done,
    bist_fail,
    irq
);
input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [31:0] wr_data;
input rd_en;
input [7:0] rd_addr;
input bist_start;
output [31:0] rd_data;
output ready;
output bist_done;
output bist_fail;
output irq;

wire [31:0] rd_data_w;
wire ready_w;
wire bist_done_w;
wire bist_fail_w;
wire irq_w;

wire sram_dout;
wire sram_csb;
wire sram_web;
wire sram_addr;
wire sram_din;

wire irq_enable;
wire mem_write_req;
wire mem_read_req;
wire bist_req;
wire bist_clear_result;
wire mem_addr_lat;
wire mem_wdata_lat;
wire irq_status_done;
wire irq_status_fail;
wire bist_running;
wire last_fail_addr;

assign rd_data = rd_data_w;
assign ready = ready_w;
assign bist_done = bist_done_w;
assign bist_fail = bist_fail_w;
assign irq = irq_w;

sram_mbist_demo_controller_regs u_regs (
    .clk(clk),
    .reset_n(reset_n),
    .wr_en(wr_en),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_addr(rd_addr),
    .bist_start(bist_start),
    .sram_dout(sram_dout),
    .ready(ready_w),
    .rd_data(rd_data_w),
    .bist_done(bist_done_w),
    .bist_fail(bist_fail_w),
    .irq(irq_w),
    .sram_csb(sram_csb),
    .sram_web(sram_web),
    .sram_addr(sram_addr),
    .sram_din(sram_din),
    .irq_enable(irq_enable),
    .mem_write_req(mem_write_req),
    .mem_read_req(mem_read_req),
    .bist_req(bist_req),
    .bist_clear_result(bist_clear_result),
    .mem_addr_lat(mem_addr_lat),
    .mem_wdata_lat(mem_wdata_lat),
    .irq_status_done(irq_status_done),
    .irq_status_fail(irq_status_fail),
    .bist_running(bist_running),
    .last_fail_addr(last_fail_addr)
);

demo_sram_32x64_model u_sram_model (
    .clk(clk),
    .csb(sram_csb),
    .web(sram_web),
    .addr(sram_addr),
    .din(sram_din),
    .dout(sram_dout)
);

endmodule
