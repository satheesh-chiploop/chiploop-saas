module fpga_block_ram_generic (
    input clk,
    input mem_csb,
    input mem_we,
    input [3:0] mem_addr,
    input [127:0] mem_din,
    output reg [127:0] mem_dout
);
    reg [127:0] mem [0:15];
    always @(posedge clk) begin
        if (!mem_csb) begin
            if (mem_we)
                mem[mem_addr] <= mem_din;
            mem_dout <= mem[mem_addr];
        end
    end
endmodule
