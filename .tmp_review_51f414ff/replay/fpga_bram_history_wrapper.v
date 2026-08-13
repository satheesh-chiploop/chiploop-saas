module fpga_bram_history_wrapper (
    input clk,
    input csb,
    input we,
    input [5:0] addr,
    input [31:0] din,
    output reg [31:0] dout
);
    reg [31:0] mem [0:63];
    always @(posedge clk) begin
        if (!csb) begin
            if (we)
                mem[addr] <= din;
            dout <= mem[addr];
        end
    end
endmodule
