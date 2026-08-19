module safety_supervisor (
    clk,
    reset_n,
    config_valid,
    request_invalid,
    response_valid,
    response_seq_mismatch,
    stale_fault,
    invalid_payload_fault,
    timeout_expired,
    safe_mode_select,
    clear_faults,
    busy,
    response_seq,
    current_sequence,
    fault_pending,
    allow_command_update,
    actuator_enable,
    fault_latched
);
    input clk;
    input reset_n;
    input config_valid;
    input request_invalid;
    input response_valid;
    input response_seq_mismatch;
    input stale_fault;
    input invalid_payload_fault;
    input timeout_expired;
    input safe_mode_select;
    input clear_faults;
    input busy;
    input [15:0] response_seq;
    output [15:0] current_sequence;
    output fault_pending;
    output allow_command_update;
    output actuator_enable;
    output fault_latched;

    reg [15:0] current_sequence_r;
    reg fault_pending_r;
    reg allow_command_update_r;
    reg actuator_enable_r;
    reg fault_latched_r;

    assign current_sequence = current_sequence_r;
    assign fault_pending = fault_pending_r;
    assign allow_command_update = allow_command_update_r;
    assign actuator_enable = actuator_enable_r;
    assign fault_latched = fault_latched_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_sequence_r <= 16'h0000;
            fault_pending_r <= 1'b0;
            allow_command_update_r <= 1'b0;
            actuator_enable_r <= 1'b0;
            fault_latched_r <= 1'b0;
        end else begin
            if (clear_faults && !request_invalid && !stale_fault && !invalid_payload_fault && !timeout_expired && !response_seq_mismatch) begin
                fault_pending_r <= 1'b0;
                fault_latched_r <= 1'b0;
            end
            if (request_invalid || response_seq_mismatch || stale_fault || invalid_payload_fault || timeout_expired) begin
                fault_pending_r <= 1'b1;
                fault_latched_r <= 1'b1;
            end
            if (config_valid && busy) begin
                current_sequence_r <= response_seq;
            end
            allow_command_update_r <= response_valid & config_valid & !fault_pending_r & !safe_mode_select;
            actuator_enable_r <= response_valid & !fault_pending_r & !safe_mode_select;
        end
    end

endmodule
