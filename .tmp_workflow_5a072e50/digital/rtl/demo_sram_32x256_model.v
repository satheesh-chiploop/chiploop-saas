module demo_sram_32x256_model (
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
reg [31:0] dout;
reg [31:0] mem [0:255];

always @(posedge clk) begin
    if (!csb) begin
        if (!web) begin
            mem[addr] <= din;
        end else begin
            dout <= mem[addr];
        end
    end
end

endmodule
