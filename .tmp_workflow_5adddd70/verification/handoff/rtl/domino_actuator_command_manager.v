module domino_actuator_command_manager (
    clk,
    rst_n,
    cfg_enable,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_safe_fallback_command_value,
    cfg_mode_select_fallback_when_valid,
    cfg_fault,
    geometry_fault,
    flow_fault,
    request_timeout_fault,
    stale_response_fault,
    response_mismatch_fault,
    model_unavailable_fault,
    validated_model_intent,
    validated_model_intent_valid,
    validated_response_valid,
    safe_fallback_request,
    actuator_cmd_valid,
    actuator_cmd,
    actuator_cmd_safe_fallback,
    cmd_clamped,
    status_mode_fallback,
    status_mode_model,
    status_faulted,
    status_actuator_saturation_fault,
    last_clamped,
    last_fallback
);
input clk;
input rst_n;
input cfg_enable;
input [15:0] cfg_actuator_min_limit;
input [15:0] cfg_actuator_max_limit;
input [15:0] cfg_safe_fallback_command_value;
input cfg_mode_select_fallback_when_valid;
input cfg_fault;
input geometry_fault;
input flow_fault;
input request_timeout_fault;
input stale_response_fault;
input response_mismatch_fault;
input model_unavailable_fault;
input [15:0] validated_model_intent;
input validated_model_intent_valid;
input validated_response_valid;
input safe_fallback_request;
output reg actuator_cmd_valid;
output reg [15:0] actuator_cmd;
output reg actuator_cmd_safe_fallback;
output reg cmd_clamped;
output reg status_mode_fallback;
output reg status_mode_model;
output reg status_faulted;
output reg status_actuator_saturation_fault;
output reg last_clamped;
output reg last_fallback;
reg [15:0] selected_cmd;

always @(*) begin
    selected_cmd = cfg_safe_fallback_command_value;
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        actuator_cmd_valid <= 1'b0;
        actuator_cmd <= 16'h0000;
        actuator_cmd_safe_fallback <= 1'b1;
        cmd_clamped <= 1'b0;
        status_mode_fallback <= 1'b1;
        status_mode_model <= 1'b0;
        status_faulted <= 1'b1;
        status_actuator_saturation_fault <= 1'b0;
        last_clamped <= 1'b0;
        last_fallback <= 1'b1;
    end else begin
        status_faulted <= (~cfg_enable) | cfg_fault | geometry_fault | flow_fault | request_timeout_fault | stale_response_fault | response_mismatch_fault | model_unavailable_fault;
        if ((~cfg_enable) | cfg_fault | geometry_fault | flow_fault | request_timeout_fault | stale_response_fault | response_mismatch_fault | model_unavailable_fault | safe_fallback_request | cfg_mode_select_fallback_when_valid | ~validated_model_intent_valid | ~validated_response_valid) begin
            actuator_cmd <= cfg_safe_fallback_command_value;
            actuator_cmd_safe_fallback <= 1'b1;
            status_mode_fallback <= 1'b1;
            status_mode_model <= 1'b0;
            last_fallback <= 1'b1;
        end else begin
            actuator_cmd <= validated_model_intent;
            actuator_cmd_safe_fallback <= 1'b0;
            status_mode_fallback <= 1'b0;
            status_mode_model <= 1'b1;
            last_fallback <= 1'b0;
        end
        if (actuator_cmd < cfg_actuator_min_limit) begin
            actuator_cmd <= cfg_actuator_min_limit;
            cmd_clamped <= 1'b1;
            last_clamped <= 1'b1;
            status_actuator_saturation_fault <= 1'b1;
        end else if (actuator_cmd > cfg_actuator_max_limit) begin
            actuator_cmd <= cfg_actuator_max_limit;
            cmd_clamped <= 1'b1;
            last_clamped <= 1'b1;
            status_actuator_saturation_fault <= 1'b1;
        end else begin
            cmd_clamped <= 1'b0;
            last_clamped <= 1'b0;
        end
        actuator_cmd_valid <= 1'b1;
    end
end
endmodule
