module request_response_fifo_bram (
    input clk,
    input csb,
    input we,
    input [3:0] addr,
    input [95:0] din,
    output reg [95:0] dout
);
    reg [95:0] mem [0:15];
    always @(posedge clk) begin
        if (!csb) begin
            if (we)
                mem[addr] <= din;
            dout <= mem[addr];
        end
    end
endmodule
