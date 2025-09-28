module sixteen_bit_counter (
    input wire clk,
    input wire reset,
    output reg [15:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000; // Reset value
    end else begin
        count <= count + 1'b1; // Increment counter on positive edge of clock
    end
end

endmodule


In this code, we have designed a 16-bit counter with a single always block that takes care of the synchronous reset and incrementing the counter on the rising edge of the clock signal. The reset value for the counter is set to `4'b0000`.