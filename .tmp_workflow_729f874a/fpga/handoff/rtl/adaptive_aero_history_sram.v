module adaptive_aero_history_sram (
    input clk,
    input csb,
    input web,
    input [7:0] addr,
    input [63:0] din,
    output reg [63:0] dout
);
    reg [63:0] mem [0:255];
    always @(posedge clk) begin
        if (!csb) begin
            if (web)
                mem[addr] <= din;
            dout <= mem[addr];
        end
    end
endmodule
