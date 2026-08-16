module adaptive_aero_command_safety (
    input clk,
    input reset_n,
    input [15:0] cfg_actuator_min,
    input [15:0] cfg_actuator_max,
    input [15:0] cfg_rate_limit,
    input [15:0] cfg_safe_fallback_cmd,
    input response_accepted,
    input [15:0] response_suggestion,
    input response_validity_ok,
    input response_fresh_ok,
    input fault_timeout,
    input fault_stale,
    input fault_sequence_mismatch,
    input fault_invalid_packet,
    input fault_transport_error,
    output reg actuator_valid,
    output reg [15:0] actuator_cmd,
    output reg safe_fallback_active,
    output reg command_clamp_active,
    output reg fallback_active_latched
);

reg [15:0] prev_cmd;
reg [15:0] clamped_cmd;
reg [15:0] rate_delta;
reg [15:0] target_cmd;
reg signed [16:0] signed_delta;
reg [15:0] delta_abs;
reg clamp_needed;
reg fallback_now;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        actuator_valid <= 1'b0;
        actuator_cmd <= 16'h0000;
        safe_fallback_active <= 1'b1;
        command_clamp_active <= 1'b0;
        fallback_active_latched <= 1'b1;
        prev_cmd <= 16'h0000;
    end else begin
        actuator_valid <= 1'b0;
        command_clamp_active <= 1'b0;
        fallback_now = fault_timeout | fault_stale | fault_sequence_mismatch | fault_invalid_packet | fault_transport_error | ~response_validity_ok | ~response_fresh_ok;
        if (response_accepted && response_validity_ok && response_fresh_ok && !fallback_now) begin
            target_cmd = response_suggestion;
            clamp_needed = 1'b0;
            if (target_cmd < cfg_actuator_min) begin
                clamped_cmd = cfg_actuator_min;
                clamp_needed = 1'b1;
            end else if (target_cmd > cfg_actuator_max) begin
                clamped_cmd = cfg_actuator_max;
                clamp_needed = 1'b1;
            end else begin
                clamped_cmd = target_cmd;
            end
            signed_delta = {1'b0, clamped_cmd} - {1'b0, prev_cmd};
            if (signed_delta < 0) delta_abs = -signed_delta[15:0];
            else delta_abs = signed_delta[15:0];
            if (cfg_rate_limit != 16'h0000 && delta_abs > cfg_rate_limit) begin
                if (clamped_cmd > prev_cmd) actuator_cmd <= prev_cmd + cfg_rate_limit;
                else actuator_cmd <= prev_cmd - cfg_rate_limit;
                command_clamp_active <= 1'b1;
            end else begin
                actuator_cmd <= clamped_cmd;
                command_clamp_active <= clamp_needed;
            end
            prev_cmd <= actuator_cmd;
            actuator_valid <= 1'b1;
            safe_fallback_active <= 1'b0;
            fallback_active_latched <= 1'b0;
        end else if (fallback_now) begin
            actuator_cmd <= (cfg_safe_fallback_cmd < cfg_actuator_min) ? cfg_actuator_min :
                            (cfg_safe_fallback_cmd > cfg_actuator_max) ? cfg_actuator_max : cfg_safe_fallback_cmd;
            actuator_valid <= 1'b1;
            safe_fallback_active <= 1'b1;
            fallback_active_latched <= 1'b1;
            prev_cmd <= actuator_cmd;
        end else begin
            safe_fallback_active <= fallback_active_latched;
        end
    end
end

endmodule
