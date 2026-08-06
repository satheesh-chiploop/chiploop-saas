module safety_supervisor (
    clk,
    reset_n,
    geometry_reject,
    envelope_fault,
    response_mismatch,
    response_fresh,
    stale_response,
    model_output_valid,
    command_clamped,
    fault_in,
    request_outstanding,
    safe_mode,
    supervisor_release,
    fallback_active,
    stale_command,
    fault_code
);
input clk;
input reset_n;
input geometry_reject;
input envelope_fault;
input response_mismatch;
input response_fresh;
input stale_response;
input model_output_valid;
input command_clamped;
input fault_in;
input request_outstanding;
output safe_mode;
output supervisor_release;
output fallback_active;
output stale_command;
output [3:0] fault_code;
reg safe_mode_r;
reg supervisor_release_r;
reg fallback_active_r;
reg stale_command_r;
reg [3:0] fault_code_r;
always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        safe_mode_r <= 1'b1;
        supervisor_release_r <= 1'b0;
        fallback_active_r <= 1'b1;
        stale_command_r <= 1'b0;
        fault_code_r <= 4'h0;
    end else begin
        safe_mode_r <= geometry_reject | envelope_fault | response_mismatch | stale_response | ~response_fresh | ~model_output_valid | fault_in | command_clamped | request_outstanding;
        supervisor_release_r <= ~(geometry_reject | envelope_fault | response_mismatch | stale_response | fault_in | command_clamped);
        fallback_active_r <= geometry_reject | envelope_fault | response_mismatch | stale_response | ~response_fresh | ~model_output_valid | fault_in | request_outstanding;
        stale_command_r <= request_outstanding & (stale_response | response_mismatch | ~response_fresh);
        fault_code_r[0] <= geometry_reject;
        fault_code_r[1] <= envelope_fault;
        fault_code_r[2] <= stale_response | ~response_fresh;
        fault_code_r[3] <= response_mismatch | fault_in;
    end
end

assign safe_mode = safe_mode_r;
assign supervisor_release = supervisor_release_r;
assign fallback_active = fallback_active_r;
assign stale_command = stale_command_r;
assign fault_code = fault_code_r;

endmodule
