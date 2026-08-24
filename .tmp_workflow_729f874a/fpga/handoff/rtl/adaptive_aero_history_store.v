module adaptive_aero_history_store (
    input clk,
    input reset_n,
    input wr_en,
    input [7:0] wr_addr,
    input [63:0] wr_data,
    input [7:0] rd_addr,
    output [63:0] rd_data,
    input rd_en
);

wire [63:0] sram_dout;
assign rd_data = sram_dout;

adaptive_aero_history_sram u_history_sram (
    .clk(clk),
    .csb(~(wr_en | rd_en)),
    .web(~wr_en),
    .addr(wr_en ? wr_addr : rd_addr),
    .din(wr_data),
    .dout(sram_dout)
);

endmodule
