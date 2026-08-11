module command_validator (
    input         clk,
    input         reset_n,
    input         packet_accept,
    input         packet_error,
    input  [7:0] sequence_id,
    input  [7:0] age_counter,
    input  [15:0] command_value,
    input  [3:0] command_mode,
    input  [7:0] fault_flags,
    input         checksum_ok,
    input  [7:0] sequence_window,
    output reg [7:0] last_accepted_sequence,
    output reg    valid_command_seen,
    output reg    stale_reject,
    output reg    checksum_fault,
    output reg    parser_error,
    output reg [15:0] validated_command_value,
    output reg [3:0] validated_command_mode,
    output reg [7:0] validated_fault_flags,
    output reg [7:0] validated_sequence_id,
    output reg [7:0] validated_age_counter
);

reg [7:0] seq_delta;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        last_accepted_sequence <= 8'd0;
        valid_command_seen <= 1'b0;
        stale_reject <= 1'b0;
        checksum_fault <= 1'b0;
        parser_error <= 1'b0;
        validated_command_value <= 16'd0;
        validated_command_mode <= 4'd0;
        validated_fault_flags <= 8'd0;
        validated_sequence_id <= 8'd0;
        validated_age_counter <= 8'd0;
        seq_delta <= 8'd0;
    end else begin
        valid_command_seen <= 1'b0;
        stale_reject <= 1'b0;
        checksum_fault <= 1'b0;
        parser_error <= 1'b0;
        if (packet_accept) begin
            seq_delta <= sequence_id - last_accepted_sequence;
            if (!checksum_ok || packet_error) begin
                checksum_fault <= 1'b1;
            end else if (sequence_id == last_accepted_sequence) begin
                stale_reject <= 1'b1;
            end else if ((sequence_id < last_accepted_sequence) && (seq_delta > sequence_window)) begin
                stale_reject <= 1'b1;
            end else begin
                valid_command_seen <= 1'b1;
                last_accepted_sequence <= sequence_id;
                validated_command_value <= command_value;
                validated_command_mode <= command_mode;
                validated_fault_flags <= fault_flags;
                validated_sequence_id <= sequence_id;
                validated_age_counter <= age_counter;
            end
        end
        if (packet_error) begin
            parser_error <= 1'b1;
        end
    end
end

endmodule
