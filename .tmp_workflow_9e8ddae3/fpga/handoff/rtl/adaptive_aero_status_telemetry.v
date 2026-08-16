module adaptive_aero_status_telemetry (
    input clk,
    input reset_n,
    input response_accepted,
    input request_issued,
    input fallback_active_latched,
    input command_clamp_active,
    input fault_timeout,
    input fault_stale,
    input fault_sequence_mismatch,
    input fault_invalid_packet,
    input fault_transport_error,
    input status_clear,
    output reg [7:0] current_state,
    output reg [7:0] status_code,
    output reg [7:0] fault_flags,
    output reg [15:0] request_counter,
    output reg [15:0] response_counter,
    output reg [15:0] debug_counter0,
    output reg [15:0] debug_counter1
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        current_state <= 8'h00;
        status_code <= 8'h00;
        fault_flags <= 8'h00;
        request_counter <= 16'h0000;
        response_counter <= 16'h0000;
        debug_counter0 <= 16'h0000;
        debug_counter1 <= 16'h0000;
    end else begin
        if (status_clear) begin
            status_code <= 8'h00;
            fault_flags <= 8'h00;
        end
        if (request_issued) request_counter <= request_counter + 16'h0001;
        if (response_accepted) response_counter <= response_counter + 16'h0001;
        if (request_issued && !response_accepted) current_state <= 8'h11;
        else if (response_accepted) current_state <= 8'h21;
        else if (fallback_active_latched) current_state <= 8'h31;
        else current_state <= 8'h01;
        status_code <= {4'b0000, fallback_active_latched, command_clamp_active, fault_timeout | fault_stale, fault_sequence_mismatch | fault_invalid_packet | fault_transport_error};
        fault_flags <= {fault_transport_error, fault_invalid_packet, fault_sequence_mismatch, command_clamp_active, fallback_active_latched, fault_stale, fault_timeout, 1'b0};
        if (request_issued) debug_counter0 <= debug_counter0 + 16'h0001;
        if (response_accepted) debug_counter1 <= debug_counter1 + 16'h0001;
    end
end

endmodule
