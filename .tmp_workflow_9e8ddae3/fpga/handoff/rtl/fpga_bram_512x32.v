module fpga_bram_512x32 (
    input clk,
    input csb,
    input web,
    input [8:0] addr,
    input [31:0] din,
    output reg [31:0] dout
);

reg [31:0] mem [0:511];
reg [8:0] addr_r;

always @(posedge clk) begin
    if (!csb) begin
        addr_r <= addr;
        if (!web) mem[addr] <= din;
        dout <= mem[addr_r];
    end
end

endmodule
