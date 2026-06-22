module demo_sram_32x256_wrapper (
    input clk,
    input csb,
    input web,
    input [7:0] addr,
    input [31:0] din,
    output [31:0] dout
);
    assign dout = 32'h00000000;
endmodule
