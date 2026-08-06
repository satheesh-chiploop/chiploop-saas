module domino_telemetry_fabric (
    clk,
    rst_n,
    telemetry_ready,
    status_mode_fallback,
    status_mode_model,
    status_faulted,
    status_stale_rejected,
    status_req_id,
    status_rsp_id,
    status_cfg_fault,
    status_geometry_fault,
    status_flow_fault,
    status_request_timeout_fault,
    status_stale_response_fault,
    status_response_mismatch_fault,
    status_model_unavailable_fault,
    status_actuator_saturation_fault,
    cmd_clamped,
    actuator_cmd_safe_fallback,
    telemetry_valid,
    telemetry_mode,
    telemetry_fault_bits,
    telemetry_stale,
    telemetry_req_id,
    telemetry_rsp_id,
    telemetry_last_clamped,
    telemetry_last_fallback
);
input clk;
input rst_n;
input telemetry_ready;
input status_mode_fallback;
input status_mode_model;
input status_faulted;
input status_stale_rejected;
input [31:0] status_req_id;
input [31:0] status_rsp_id;
input status_cfg_fault;
input status_geometry_fault;
input status_flow_fault;
input status_request_timeout_fault;
input status_stale_response_fault;
input status_response_mismatch_fault;
input status_model_unavailable_fault;
input status_actuator_saturation_fault;
input cmd_clamped;
input actuator_cmd_safe_fallback;
output reg telemetry_valid;
output reg [1:0] telemetry_mode;
output reg [7:0] telemetry_fault_bits;
output reg telemetry_stale;
output reg [31:0] telemetry_req_id;
output reg [31:0] telemetry_rsp_id;
output reg telemetry_last_clamped;
output reg telemetry_last_fallback;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        telemetry_valid <= 1'b0;
        telemetry_mode <= 2'b00;
        telemetry_fault_bits <= 8'h00;
        telemetry_stale <= 1'b0;
        telemetry_req_id <= 32'h00000000;
        telemetry_rsp_id <= 32'h00000000;
        telemetry_last_clamped <= 1'b0;
        telemetry_last_fallback <= 1'b1;
    end else begin
        telemetry_valid <= telemetry_ready;
        telemetry_mode <= {status_mode_model, status_mode_fallback};
        telemetry_fault_bits <= {status_actuator_saturation_fault, status_model_unavailable_fault, status_response_mismatch_fault, status_stale_response_fault, status_request_timeout_fault, status_flow_fault, status_geometry_fault, status_cfg_fault};
        telemetry_stale <= status_stale_rejected;
        telemetry_req_id <= status_req_id;
        telemetry_rsp_id <= status_rsp_id;
        telemetry_last_clamped <= cmd_clamped;
        telemetry_last_fallback <= actuator_cmd_safe_fallback;
    end
end
endmodule
