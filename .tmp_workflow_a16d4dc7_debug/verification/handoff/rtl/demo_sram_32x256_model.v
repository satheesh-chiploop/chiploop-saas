module demo_sram_32x256_model (
    input clk,
    input csb,
    input web,
    input [7:0] addr,
    input [31:0] din,
    output reg [31:0] dout
);

reg [31:0] mem [0:255];
integer i;

always @(posedge clk) begin
    if (csb == 1'b0) begin
        if (web == 1'b0) begin
            mem[addr] <= din;
        end else begin
            dout <= mem[addr];
        end
    end
end

endmodule
