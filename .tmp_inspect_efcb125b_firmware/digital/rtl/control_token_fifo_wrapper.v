module control_token_fifo_wrapper (
    input             clk,
    input             reset_n,
    input             wr_en,
    input             rd_en,
    input      [63:0] wr_data,
    output reg [63:0] rd_data,
    output reg        full,
    output reg        empty,
    output reg [4:0] count
);
    reg [63:0] mem [0:7];
    reg [2:0] wr_ptr;
    reg [2:0] rd_ptr;
    reg [63:0] rd_data_n;

    always @(posedge clk) begin
        if (!reset_n) begin
            wr_ptr <= 3'd0;
            rd_ptr <= 3'd0;
            count <= 5'd0;
            rd_data <= 64'd0;
            full <= 1'b0;
            empty <= 1'b1;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr] <= wr_data;
                wr_ptr <= wr_ptr + 3'd1;
                count <= count + 5'd1;
            end
            if (rd_en && !empty) begin
                rd_data <= mem[rd_ptr];
                rd_ptr <= rd_ptr + 3'd1;
                count <= count - 5'd1;
            end
            full <= (count == 5'd8);
            empty <= (count == 5'd0);
        end
    end
endmodule
