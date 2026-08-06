module clamp_unit (
    input         clk,
    input         rst_n,
    input  [31:0] command_in,
    input         command_valid_in,
    input  [31:0] command_min_in,
    input  [31:0] command_max_in,
    output [31:0] command_out,
    output        command_valid_out,
    output        clamp_active_out
);
    reg [31:0] command_out_r;
    reg command_valid_out_r;
    reg clamp_active_r;
    wire below_min;
    wire above_max;
    wire [31:0] clamped;

    assign below_min = (command_in < command_min_in);
    assign above_max = (command_in > command_max_in);
    assign clamped = below_min ? command_min_in : (above_max ? command_max_in : command_in);

    assign command_out = command_out_r;
    assign command_valid_out = command_valid_out_r;
    assign clamp_active_out = clamp_active_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            command_out_r <= 32'h0000_0000;
            command_valid_out_r <= 1'b0;
            clamp_active_r <= 1'b0;
        end else begin
            clamp_active_r <= command_valid_in & (below_min | above_max);
            command_valid_out_r <= command_valid_in;
            if (command_valid_in) begin
                command_out_r <= clamped;
            end
        end
    end
endmodule
