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

reg [31:0] dout_r;
reg [31:0] mem [0:63];

assign dout = dout_r;

always @(posedge clk) begin
    if (!csb) begin
        if (!web) begin
            mem[addr] <= din;
            dout_r <= din;
        end else begin
            dout_r <= mem[addr];
        end
    end
end

endmodule
