module adaptive_aero_history_wrapper (
    input         clk,
    input         reset_n,
    input         history_csb,
    input         history_we,
    input  [9:0]  history_addr,
    input  [63:0] history_din,
    output [63:0] history_dout
);

reg [63:0] mem [0:1023];
reg [63:0] history_dout_r;

assign history_dout = history_dout_r;

always @(posedge clk) begin
    if (!reset_n) begin
        history_dout_r <= 64'h0000000000000000;
    end else begin
        if (!history_csb) begin
            if (history_we) begin
                mem[history_addr] <= history_din;
            end
            history_dout_r <= mem[history_addr];
        end
    end
end

endmodule