module adaptive_aero_history_store (
    input         clk,
    input         reset_n,
    input  [8:0] cfg_history_base,
    input  [7:0] cfg_payload_base,
    output reg    history_busy,
    output reg    payload_busy
);

reg [127:0] mem [0:511];
reg [8:0] rd_addr;
reg [8:0] wr_addr;
reg [127:0] rd_data;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        history_busy <= 1'b0;
        payload_busy <= 1'b0;
        rd_addr <= 9'd0;
        wr_addr <= 9'd0;
        rd_data <= 128'd0;
    end else begin
        history_busy <= 1'b0;
        payload_busy <= 1'b0;
        rd_addr <= cfg_history_base;
        wr_addr <= {cfg_payload_base[6:0], 2'b00};
        mem[wr_addr] <= {103'd0, cfg_history_base, cfg_payload_base};
        rd_data <= mem[rd_addr];
    end
end

endmodule
