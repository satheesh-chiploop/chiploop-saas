module demo_sram_32x256_wrapper (
    clk,
    csb,
    web,
    addr,
    din,
    dout
);
    input clk;
    input csb;
    input web;
    input [7:0] addr;
    input [31:0] din;
    output [31:0] dout;
    wire [31:0] dout_r;
    sky130_sram_1kbyte_1rw1r_32x256_8 u_sram (
        .clk0(clk),
        .csb0(csb),
        .web0(web),
        .wmask0(4'b0000),
        .addr0(addr),
        .din0(din),
        .dout0(dout_r),
        .clk1(clk),
        .csb1(csb),
        .addr1(addr),
        .dout1()
    );

    assign dout = dout_r;
endmodule
