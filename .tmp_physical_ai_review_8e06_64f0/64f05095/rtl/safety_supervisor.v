module safety_supervisor (
    clk,
    rst_n,
    clamped_cmd_valid,
    clamped_actuator_cmd,
    fallback_cmd_valid,
    fallback_cmd,
    fallback_active,
    response_match,
    freshness_ok,
    timeout_event,
    stale_or_mismatch_fault,
    invalid_input_fault,
    payload_corruption_fault,
    model_unavailable_fault,
    cfg_load_done,
    cfg_clear_faults,
    cfg_fault_clear_sticky,
    actuator_cmd_valid,
    actuator_cmd,
    fault_valid,
    fault_code,
    source_select,
    sticky_fault_latched
);

input clk;
input rst_n;
input clamped_cmd_valid;
input [31:0] clamped_actuator_cmd;
input fallback_cmd_valid;
input [31:0] fallback_cmd;
input fallback_active;
input response_match;
input freshness_ok;
input timeout_event;
input stale_or_mismatch_fault;
input invalid_input_fault;
input payload_corruption_fault;
input model_unavailable_fault;
input cfg_load_done;
input cfg_clear_faults;
input cfg_fault_clear_sticky;
output reg actuator_cmd_valid;
output reg [31:0] actuator_cmd;
output reg fault_valid;
output reg [15:0] fault_code;
output reg source_select;
output reg sticky_fault_latched;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        actuator_cmd_valid <= 1'b1;
        actuator_cmd <= 32'h00000000;
        fault_valid <= 1'b0;
        fault_code <= 16'h0000;
        source_select <= 1'b1;
        sticky_fault_latched <= 1'b1;
    end else begin
        if (cfg_clear_faults | cfg_fault_clear_sticky) begin
            sticky_fault_latched <= 1'b0;
        end else if (timeout_event | stale_or_mismatch_fault | invalid_input_fault | payload_corruption_fault | model_unavailable_fault | ~cfg_load_done) begin
            sticky_fault_latched <= 1'b1;
        end
        fault_valid <= sticky_fault_latched | timeout_event | stale_or_mismatch_fault | invalid_input_fault | payload_corruption_fault | model_unavailable_fault | ~cfg_load_done | ~freshness_ok | ~response_match;
        fault_code <= {8'h00, timeout_event, stale_or_mismatch_fault, invalid_input_fault, payload_corruption_fault, model_unavailable_fault, ~cfg_load_done, ~freshness_ok, ~response_match};
        if (fallback_active | sticky_fault_latched | timeout_event | stale_or_mismatch_fault | invalid_input_fault | payload_corruption_fault | model_unavailable_fault | ~cfg_load_done) begin
            actuator_cmd_valid <= fallback_cmd_valid;
            actuator_cmd <= fallback_cmd;
            source_select <= 1'b1;
        end else begin
            actuator_cmd_valid <= clamped_cmd_valid;
            actuator_cmd <= clamped_actuator_cmd;
            source_select <= 1'b0;
        end
    end
end

endmodule
