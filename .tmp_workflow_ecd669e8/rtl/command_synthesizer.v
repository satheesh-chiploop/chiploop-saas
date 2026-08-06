module command_synthesizer (
    input         clk,
    input         rst_n,
    input         response_payload_valid_in,
    input  [31:0] drag_force_in,
    input  [31:0] lift_force_in,
    input  [31:0] surface_pressure_in,
    input  [63:0] flow_field_meta_in,
    input         fallback_active_in,
    output  [31:0] safe_fallback_command_in,
    output [31:0] command_raw_out,
    output        command_valid_out,
    output        command_source_fallback_out
);
    reg [31:0] command_raw_r;
    reg command_valid_r;
    reg command_source_fallback_r;
    wire [31:0] model_cmd;

    assign model_cmd = drag_force_in ^ lift_force_in ^ surface_pressure_in ^ flow_field_meta_in[31:0] ^ flow_field_meta_in[63:32];
    assign command_raw_out = command_raw_r;
    assign command_valid_out = command_valid_r;
    assign command_source_fallback_out = command_source_fallback_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            command_raw_r <= 32'h0000_0000;
            command_valid_r <= 1'b0;
            command_source_fallback_r <= 1'b1;
        end else begin
            if (fallback_active_in) begin
                command_raw_r <= safe_fallback_command_in;
                command_source_fallback_r <= 1'b1;
                command_valid_r <= 1'b1;
            end else if (response_payload_valid_in) begin
                command_raw_r <= model_cmd;
                command_source_fallback_r <= 1'b0;
                command_valid_r <= 1'b1;
            end else begin
                command_valid_r <= 1'b0;
            end
        end
    end
endmodule
