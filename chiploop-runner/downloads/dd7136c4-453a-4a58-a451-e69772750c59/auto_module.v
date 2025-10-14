module counter_4b(clk, reset, enable);

reg [3:0] count;
reg [3:0] count_next;

always @(posedge clk)
begin
    if (reset) begin
        count <= 4'b0000;
    end else if (enable) begin
        count <= count_next;
    end
end

assign count_next = count + 1'b0001;

endmodule