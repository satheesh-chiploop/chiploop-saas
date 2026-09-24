module adaptive_aero_control_top (
    input         clk,
    input         reset_n,
    input  [15:0] mmio_addr,
    input  [31:0] mmio_wdata,
    input         mmio_valid,
    input         mmio_we,
    output [31:0] mmio_rdata,
    output        mmio_ready,
    output        mmio_error,
    input         model_req_ready,
    output        model_req_valid,
    output [63:0] model_req_data,
    input         model_rsp_valid,
    input  [127:0] model_rsp_data,
    output        model_rsp_ready,
    output        actuator_cmd_valid,
    output [7:0] actuator_cmd_tilt,
    output [7:0] actuator_cmd_deflection,
    output [1:0] actuator_cmd_mode,
    output        fault_latched,
    output        status_valid,
    output [7:0] status_code
);
wire cfg_enable;
wire cfg_surrogate_select;
wire [15:0] cfg_timeout_cycles;
wire [15:0] cfg_stale_limit_cycles;
wire [7:0] cfg_tilt_limit;
wire [7:0] cfg_deflection_limit;
wire [1:0] cfg_mode_select;
wire cfg_clear_fault;
wire [8:0] cfg_history_base;
wire [7:0] cfg_payload_base;
wire status_fault_latched;
wire status_model_busy;
wire status_model_valid;
wire status_timeout_active;
wire status_stale_active;
wire [7:0] status_last_response_code;
wire [31:0] pack_vehicle_state;
wire [15:0] pack_wind_state;
wire [15:0] pack_reference_state;
wire response_valid;
wire [127:0] response_data;
wire response_stale;
wire [7:0] surrogate_tilt_cmd;
wire [7:0] surrogate_deflection_cmd;
wire [7:0] reference_tilt_cmd;
wire [7:0] reference_deflection_cmd;
wire validation_valid;
wire validation_error;
wire [7:0] validation_delta_code;
wire history_busy;
wire payload_busy;
adaptive_aero_mmio_csr u_mmio_csr (
    .clk(clk),
    .reset_n(reset_n),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_valid(mmio_valid),
    .mmio_we(mmio_we),
    .mmio_rdata(mmio_rdata),
    .mmio_ready(mmio_ready),
    .mmio_error(mmio_error),
    .cfg_enable(cfg_enable),
    .cfg_surrogate_select(cfg_surrogate_select),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_stale_limit_cycles(cfg_stale_limit_cycles),
    .cfg_tilt_limit(cfg_tilt_limit),
    .cfg_deflection_limit(cfg_deflection_limit),
    .cfg_mode_select(cfg_mode_select),
    .cfg_clear_fault(cfg_clear_fault),
    .cfg_history_base(cfg_history_base),
    .cfg_payload_base(cfg_payload_base),
    .status_fault_latched(status_fault_latched),
    .status_model_busy(status_model_busy),
    .status_model_valid(status_model_valid),
    .status_timeout_active(status_timeout_active),
    .status_stale_active(status_stale_active),
    .status_last_response_code(status_last_response_code),
    .status_valid(status_valid)
);

adaptive_aero_transport u_transport (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_surrogate_select(cfg_surrogate_select),
    .model_req_ready(model_req_ready),
    .model_req_valid(model_req_valid),
    .model_req_data(model_req_data),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(model_rsp_ready),
    .pack_vehicle_state(pack_vehicle_state),
    .pack_wind_state(pack_wind_state),
    .pack_reference_state(pack_reference_state),
    .request_busy(status_model_busy),
    .response_valid(response_valid),
    .response_data(response_data),
    .response_stale(response_stale)
);

adaptive_aero_surrogate_reference u_surrogate_reference (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_tilt_limit(cfg_tilt_limit),
    .cfg_deflection_limit(cfg_deflection_limit),
    .response_valid(response_valid),
    .response_data(response_data),
    .response_stale(response_stale),
    .pack_vehicle_state(pack_vehicle_state),
    .pack_wind_state(pack_wind_state),
    .pack_reference_state(pack_reference_state),
    .surrogate_tilt_cmd(surrogate_tilt_cmd),
    .surrogate_deflection_cmd(surrogate_deflection_cmd),
    .reference_tilt_cmd(reference_tilt_cmd),
    .reference_deflection_cmd(reference_deflection_cmd),
    .validation_valid(validation_valid),
    .validation_error(validation_error),
    .validation_delta_code(validation_delta_code)
);

adaptive_aero_safety_bounding u_safety (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_clear_fault(cfg_clear_fault),
    .cfg_tilt_limit(cfg_tilt_limit),
    .cfg_deflection_limit(cfg_deflection_limit),
    .validation_valid(validation_valid),
    .validation_error(validation_error),
    .validation_delta_code(validation_delta_code),
    .surrogate_tilt_cmd(surrogate_tilt_cmd),
    .surrogate_deflection_cmd(surrogate_deflection_cmd),
    .reference_tilt_cmd(reference_tilt_cmd),
    .reference_deflection_cmd(reference_deflection_cmd),
    .actuator_cmd_valid(actuator_cmd_valid),
    .actuator_cmd_tilt(actuator_cmd_tilt),
    .actuator_cmd_deflection(actuator_cmd_deflection),
    .actuator_cmd_mode(actuator_cmd_mode),
    .fault_latched(fault_latched),
    .status_valid(status_valid),
    .status_code(status_code),
    .status_fault_latched(status_fault_latched),
    .status_timeout_active(status_timeout_active),
    .status_stale_active(status_stale_active)
);

adaptive_aero_history_store u_history_store (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_history_base(cfg_history_base),
    .cfg_payload_base(cfg_payload_base),
    .history_busy(history_busy),
    .payload_busy(payload_busy)
);

assign status_model_valid = response_valid;
assign status_last_response_code = status_code;

endmodule
