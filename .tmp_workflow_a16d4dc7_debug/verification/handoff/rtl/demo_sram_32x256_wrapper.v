module demo_sram_32x256_wrapper (
    input clk,
    input csb,
    input web,
    input [7:0] addr,
    input [31:0] din,
    output [31:0] dout
);

demo_sram_32x256_model u_model (
    .clk(clk),
    .csb(csb),
    .web(web),
    .addr(addr),
    .din(din),
    .dout(dout)
);

endmodule
