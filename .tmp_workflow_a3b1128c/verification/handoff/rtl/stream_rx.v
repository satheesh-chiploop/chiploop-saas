module stream_rx (
    input         clk,
    input         reset_n,
    input         in_cmd_valid,
    input  [63:0] in_cmd_data,
    output reg    in_cmd_ready,
    output reg    packet_accept,
    output reg    packet_error,
    output reg [7:0] sequence_id,
    output reg [7:0] age_counter,
    output reg [15:0] command_value,
    output reg [3:0] command_mode,
    output reg [7:0] fault_flags,
    output reg    checksum_ok
);

reg [7:0] checksum_calc;
reg [7:0] pkt_checksum;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        in_cmd_ready <= 1'b0;
        packet_accept <= 1'b0;
        packet_error <= 1'b0;
        sequence_id <= 8'd0;
        age_counter <= 8'd0;
        command_value <= 16'd0;
        command_mode <= 4'd0;
        fault_flags <= 8'd0;
        checksum_ok <= 1'b0;
        checksum_calc <= 8'd0;
        pkt_checksum <= 8'd0;
    end else begin
        in_cmd_ready <= 1'b1;
        packet_accept <= 1'b0;
        packet_error <= 1'b0;
        if (in_cmd_valid && in_cmd_ready) begin
            sequence_id <= in_cmd_data[63:56];
            age_counter <= in_cmd_data[55:48];
            command_mode <= in_cmd_data[47:44];
            fault_flags <= in_cmd_data[43:36];
            command_value <= in_cmd_data[35:20];
            pkt_checksum <= in_cmd_data[7:0];
            checksum_calc <= in_cmd_data[63:56] ^ in_cmd_data[55:48] ^ in_cmd_data[47:40] ^ in_cmd_data[39:32] ^ in_cmd_data[31:24] ^ in_cmd_data[23:16] ^ in_cmd_data[15:8];
            checksum_ok <= (pkt_checksum == checksum_calc);
            packet_accept <= (pkt_checksum == checksum_calc);
            packet_error <= (pkt_checksum != checksum_calc);
        end
    end
end

endmodule
