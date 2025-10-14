module counter_4b(clk, reset, enable);

wire [3:0] count;
reg [3:0] q;

always @(posedge clk) begin
    if (reset) begin
        q <= 0;
    end else if (enable) begin
        q <= q + 1'b1;
    end
end

assign count = q;

endmodule