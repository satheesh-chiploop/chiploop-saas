module adaptive_aero_response_validator (
    input clk,
    input reset_n,
    input resp_valid,
    input [127:0] resp_data,
    output reg resp_ready,
    input [15:0] request_seq,
    input [15:0] request_timestamp,
    input request_context_valid,
    input [15:0] cfg_timeout_limit,
    input [15:0] cfg_stale_age_limit,
    input cfg_enable,
    input timeout_expired,
    input [15:0] current_cycle_age,
    output reg response_accepted,
    output reg response_rejected,
    output reg [15:0] response_seq,
    output reg [15:0] response_suggestion,
    output reg [7:0] response_status_flags,
    output reg response_validity_ok,
    output reg response_fresh_ok,
    output reg fault_timeout,
    output reg fault_stale,
    output reg fault_sequence_mismatch,
    output reg fault_invalid_packet,
    output reg fault_transport_error
);

wire seq_match;
wire fresh_ok;
wire valid_bits_ok;
wire transport_ok;
wire timeout_ok;

assign seq_match = (resp_data[15:0] == request_seq);
assign fresh_ok = (current_cycle_age <= cfg_stale_age_limit);
assign valid_bits_ok = (resp_data[95:88] == 8'hA5);
assign transport_ok = resp_data[127];
assign timeout_ok = ~timeout_expired;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        resp_ready <= 1'b0;
        response_accepted <= 1'b0;
        response_rejected <= 1'b0;
        response_seq <= 16'h0000;
        response_suggestion <= 16'h0000;
        response_status_flags <= 8'h00;
        response_validity_ok <= 1'b0;
        response_fresh_ok <= 1'b0;
        fault_timeout <= 1'b0;
        fault_stale <= 1'b0;
        fault_sequence_mismatch <= 1'b0;
        fault_invalid_packet <= 1'b0;
        fault_transport_error <= 1'b0;
    end else begin
        resp_ready <= cfg_enable & request_context_valid;
        response_accepted <= 1'b0;
        response_rejected <= 1'b0;
        response_validity_ok <= 1'b0;
        response_fresh_ok <= 1'b0;
        if (resp_valid && resp_ready) begin
            response_seq <= resp_data[15:0];
            response_suggestion <= resp_data[31:16];
            response_status_flags <= resp_data[87:80];
            response_validity_ok <= valid_bits_ok;
            response_fresh_ok <= fresh_ok;
            if (request_context_valid && seq_match && fresh_ok && timeout_ok && valid_bits_ok && transport_ok) begin
                response_accepted <= 1'b1;
                fault_timeout <= 1'b0;
                fault_stale <= 1'b0;
                fault_sequence_mismatch <= 1'b0;
                fault_invalid_packet <= 1'b0;
                fault_transport_error <= 1'b0;
            end else begin
                response_rejected <= 1'b1;
                fault_timeout <= ~timeout_ok;
                fault_stale <= ~fresh_ok;
                fault_sequence_mismatch <= ~(request_context_valid && seq_match);
                fault_invalid_packet <= ~valid_bits_ok;
                fault_transport_error <= ~transport_ok;
            end
        end
        if (!cfg_enable) begin
            fault_timeout <= 1'b0;
            fault_stale <= 1'b0;
            fault_sequence_mismatch <= 1'b0;
            fault_invalid_packet <= 1'b0;
            fault_transport_error <= 1'b0;
        end
    end
end

endmodule
