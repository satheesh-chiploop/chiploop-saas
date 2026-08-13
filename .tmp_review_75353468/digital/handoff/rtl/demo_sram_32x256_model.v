module demo_sram_32x256_model (
    clk,
    csb,
    web,
    addr,
    din,
    dout
);
    input clk;
    input csb;
    input web;
    input [7:0] addr;
    input [31:0] din;
    output [31:0] dout;
    reg [31:0] mem [0:255];
    reg [31:0] dout_r;
    reg [31:0] read_data;

    assign dout = dout_r;

    always @(*) begin
        read_data = dout_r;
    end

    always @(posedge clk) begin
        if (!csb) begin
            if (!web) begin
                mem[addr] <= din;
            end else begin
                dout_r <= mem[addr];
            end
        end
    end
endmodule
