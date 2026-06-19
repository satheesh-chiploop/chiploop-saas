module demo_sram_32x64_model (
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
input [5:0] addr;
input [31:0] din;
output [31:0] dout;

reg [31:0] mem [0:63];
reg [31:0] dout_reg;

assign dout = dout_reg;

integer i;

initial begin
    for (i = 0; i < 64; i = i + 1) begin
        mem[i] = 32'b00000000000000000000000000000000;
    end
    dout_reg = 32'b00000000000000000000000000000000;
end

always @(posedge clk) begin
    if (!csb) begin
        if (!web) begin
            mem[addr] <= din;
            dout_reg <= din;
        end else begin
            dout_reg <= mem[addr];
        end
    end
end

endmodule
