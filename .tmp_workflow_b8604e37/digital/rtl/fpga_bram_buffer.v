module fpga_bram_buffer (
    input clk,
    input csb,
    input we,
    input [3:0] addr,
    input [127:0] din,
    output reg [127:0] dout
);
    reg [127:0] mem [0:15];
    always @(posedge clk) begin
        if (!csb) begin
            if (we)
                mem[addr] <= din;
            dout <= mem[addr];
        end
    end
endmodule
