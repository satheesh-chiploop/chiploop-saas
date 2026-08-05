module safe_fallback_manager (
    clk,
    rst_n,
    cfg_load_done,
    fault_in,
    timeout_event,
    stale_or_mismatch_fault,
    payload_corruption_fault,
    model_unavailable_fault,
    invalid_input_fault,
    cfg_safe_actuator_cmd,
    fallback_cmd,
    fallback_cmd_valid,
    fallback_active
);

input clk;
input rst_n;
input cfg_load_done;
input fault_in;
input timeout_event;
input stale_or_mismatch_fault;
input payload_corruption_fault;
input model_unavailable_fault;
input invalid_input_fault;
input [31:0] cfg_safe_actuator_cmd;
output reg [31:0] fallback_cmd;
output reg fallback_cmd_valid;
output reg fallback_active;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        fallback_cmd <= 32'h00000000;
        fallback_cmd_valid <= 1'b1;
        fallback_active <= 1'b1;
    end else begin
        fallback_active <= ~cfg_load_done | fault_in | timeout_event | stale_or_mismatch_fault | payload_corruption_fault | model_unavailable_fault | invalid_input_fault;
        fallback_cmd_valid <= 1'b1;
        if (~cfg_load_done | fault_in | timeout_event | stale_or_mismatch_fault | payload_corruption_fault | model_unavailable_fault | invalid_input_fault) begin
            fallback_cmd <= cfg_safe_actuator_cmd;
        end else begin
            fallback_cmd <= cfg_safe_actuator_cmd;
        end
    end
end

endmodule
