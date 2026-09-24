module adaptive_aero_safety_bounding (
    input         clk,
    input         reset_n,
    input         cfg_enable,
    input         cfg_clear_fault,
    input  [7:0] cfg_tilt_limit,
    input  [7:0] cfg_deflection_limit,
    input         validation_valid,
    input         validation_error,
    input  [7:0] validation_delta_code,
    input  [7:0] surrogate_tilt_cmd,
    input  [7:0] surrogate_deflection_cmd,
    input  [7:0] reference_tilt_cmd,
    input  [7:0] reference_deflection_cmd,
    output reg    actuator_cmd_valid,
    output reg [7:0] actuator_cmd_tilt,
    output reg [7:0] actuator_cmd_deflection,
    output reg [1:0] actuator_cmd_mode,
    output reg    fault_latched,
    output reg    status_valid,
    output reg [7:0] status_code,
    output reg    status_fault_latched,
    output reg    status_timeout_active,
    output reg    status_stale_active
);

wire [7:0] tilt_bounded;
wire [7:0] defl_bounded;
wire [7:0] validation_mix;

assign tilt_bounded = (surrogate_tilt_cmd > cfg_tilt_limit) ? cfg_tilt_limit : surrogate_tilt_cmd;
assign defl_bounded = (surrogate_deflection_cmd > cfg_deflection_limit) ? cfg_deflection_limit : surrogate_deflection_cmd;
assign validation_mix = validation_delta_code ^ reference_tilt_cmd ^ reference_deflection_cmd;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        actuator_cmd_valid <= 1'b0;
        actuator_cmd_tilt <= 8'd0;
        actuator_cmd_deflection <= 8'd0;
        actuator_cmd_mode <= 2'b00;
        fault_latched <= 1'b0;
        status_valid <= 1'b0;
        status_code <= 8'd0;
        status_fault_latched <= 1'b0;
        status_timeout_active <= 1'b0;
        status_stale_active <= 1'b0;
    end else begin
        status_fault_latched <= fault_latched;
        status_timeout_active <= validation_error;
        status_stale_active <= ~validation_valid;
        if (cfg_clear_fault) fault_latched <= 1'b0;
        if (validation_error || !validation_valid || !cfg_enable) begin
            actuator_cmd_valid <= 1'b0;
            fault_latched <= fault_latched | validation_error | ~cfg_enable;
            status_valid <= 1'b0;
            status_code <= validation_mix;
        end else begin
            actuator_cmd_valid <= 1'b1;
            actuator_cmd_tilt <= tilt_bounded;
            actuator_cmd_deflection <= defl_bounded;
            actuator_cmd_mode <= 2'b01;
            status_valid <= 1'b1;
            status_code <= validation_mix;
        end
    end
end

endmodule
