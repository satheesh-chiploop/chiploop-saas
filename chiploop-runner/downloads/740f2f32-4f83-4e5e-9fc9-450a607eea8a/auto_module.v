module auto_module(  
    input  wire clk,
    input  wire reset,
    input  wire [3:0] counter_en,
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
    end else if (counter_en) begin
        count <= count + 1;
    end
end

endmodule