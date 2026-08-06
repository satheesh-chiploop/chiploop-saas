module domino_active_aero_control_wrapper (
    clk,
    rst_n,
    host_cfg_valid,
    host_cfg_write,
    host_cfg_addr,
    host_cfg_wdata,
    host_cfg_ready,
    host_cfg_rdata,
    host_cfg_rvalid,
    enable,
    freshness_timeout_cycles,
    request_timeout_cycles,
    actuator_min_limit,
    actuator_max_limit,
    safe_fallback_command_value,
    stream_velocity_mps,
    flow_update_strobe,
    geometry_update_strobe,
    geometry_format_selector,
    geometry_metadata_valid,
    geometry_metadata_tag,
    geometry_handle_in,
    geometry_reference_is_driaverml_stl,
    fault_clear,
    mode_select_fallback_when_valid,
    model_req_ready,
    model_rsp_valid,
    model_rsp_id,
    model_rsp_epoch,
    model_rsp_status_valid,
    model_rsp_status_unavailable,
    model_rsp_drag_force,
    model_rsp_lift_force,
    model_rsp_surface_pressure,
    model_rsp_flow_field_meta,
    model_req_valid,
    model_req_id,
    model_req_epoch,
    model_req_geometry_handle,
    model_req_stream_velocity_mps,
    model_req_timeout_cycles,
    actuator_cmd_valid,
    actuator_cmd,
    actuator_cmd_safe_fallback,
    cmd_clamped,
    status_mode_fallback,
    status_mode_model,
    status_stale_rejected,
    status_faulted,
    status_req_id,
    status_rsp_id,
    status_last_accepted_req_id,
    status_last_accepted_rsp_id,
    status_cfg_fault,
    status_geometry_fault,
    status_flow_fault,
    status_request_timeout_fault,
    status_stale_response_fault,
    status_response_mismatch_fault,
    status_model_unavailable_fault,
    status_actuator_saturation_fault,
    telemetry_valid,
    telemetry_ready,
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
input host_cfg_valid;
input host_cfg_write;
input [7:0] host_cfg_addr;
input [31:0] host_cfg_wdata;
output host_cfg_ready;
output [31:0] host_cfg_rdata;
output host_cfg_rvalid;
input enable;
input [15:0] freshness_timeout_cycles;
input [15:0] request_timeout_cycles;
input [15:0] actuator_min_limit;
input [15:0] actuator_max_limit;
input [15:0] safe_fallback_command_value;
input [15:0] stream_velocity_mps;
input flow_update_strobe;
input geometry_update_strobe;
input [7:0] geometry_format_selector;
input geometry_metadata_valid;
input [15:0] geometry_metadata_tag;
input [31:0] geometry_handle_in;
input geometry_reference_is_driaverml_stl;
input fault_clear;
input mode_select_fallback_when_valid;
input model_req_ready;
input model_rsp_valid;
input [31:0] model_rsp_id;
input [31:0] model_rsp_epoch;
input model_rsp_status_valid;
input model_rsp_status_unavailable;
input [31:0] model_rsp_drag_force;
input [31:0] model_rsp_lift_force;
input [31:0] model_rsp_surface_pressure;
input [31:0] model_rsp_flow_field_meta;
output model_req_valid;
output [31:0] model_req_id;
output [31:0] model_req_epoch;
output [31:0] model_req_geometry_handle;
output [15:0] model_req_stream_velocity_mps;
output [15:0] model_req_timeout_cycles;
output actuator_cmd_valid;
output [15:0] actuator_cmd;
output actuator_cmd_safe_fallback;
output cmd_clamped;
output status_mode_fallback;
output status_mode_model;
output status_stale_rejected;
output status_faulted;
output [31:0] status_req_id;
output [31:0] status_rsp_id;
output [31:0] status_last_accepted_req_id;
output [31:0] status_last_accepted_rsp_id;
output status_cfg_fault;
output status_geometry_fault;
output status_flow_fault;
output status_request_timeout_fault;
output status_stale_response_fault;
output status_response_mismatch_fault;
output status_model_unavailable_fault;
output status_actuator_saturation_fault;
output telemetry_valid;
input telemetry_ready;
output [1:0] telemetry_mode;
output [7:0] telemetry_fault_bits;
output telemetry_stale;
output [31:0] telemetry_req_id;
output [31:0] telemetry_rsp_id;
output telemetry_last_clamped;
output telemetry_last_fallback;

wire cfg_enable;
wire [15:0] cfg_freshness_timeout_cycles;
wire [15:0] cfg_request_timeout_cycles;
wire [15:0] cfg_actuator_min_limit;
wire [15:0] cfg_actuator_max_limit;
wire [15:0] cfg_safe_fallback_command_value;
wire [15:0] cfg_stream_velocity_low_limit;
wire [15:0] cfg_stream_velocity_high_limit;
wire [7:0] cfg_geometry_format_selector;
wire cfg_fault_clear;
wire cfg_mode_select_fallback_when_valid;
wire cfg_fault;
wire [31:0] flow_epoch;
wire [31:0] geometry_epoch;
wire [31:0] active_epoch;
wire [15:0] validated_stream_velocity_mps;
wire [31:0] geometry_handle_canonical;
wire geometry_valid;
wire flow_valid;
wire geometry_fault;
wire flow_fault;
wire envelope_in_range;
wire input_update_strobe;
wire request_outstanding;
wire request_timeout_fault;
wire [31:0] last_issued_req_id;
wire validated_response_valid;
wire [31:0] validated_rsp_id;
wire [31:0] validated_rsp_epoch;
wire response_mismatch_fault;
wire stale_response_fault;
wire model_unavailable_fault;
wire [15:0] validated_model_intent;
wire validated_model_intent_valid;
wire stale_status;
wire status_actuator_saturation_fault_i;
wire status_faulted_i;
wire status_mode_fallback_i;
wire status_mode_model_i;
wire cmd_clamped_i;
wire actuator_cmd_safe_fallback_i;
wire telemetry_valid_i;
wire [1:0] telemetry_mode_i;
wire [7:0] telemetry_fault_bits_i;
wire telemetry_stale_i;
wire [31:0] telemetry_req_id_i;
wire [31:0] telemetry_rsp_id_i;
wire telemetry_last_clamped_i;
wire telemetry_last_fallback_i;
wire host_cfg_ready_i;
wire [31:0] host_cfg_rdata_i;
wire host_cfg_rvalid_i;
wire request_arm;

assign cfg_enable = enable;
assign cfg_freshness_timeout_cycles = freshness_timeout_cycles;
assign cfg_request_timeout_cycles = request_timeout_cycles;
assign cfg_actuator_min_limit = actuator_min_limit;
assign cfg_actuator_max_limit = actuator_max_limit;
assign cfg_safe_fallback_command_value = safe_fallback_command_value;
assign cfg_stream_velocity_low_limit = freshness_timeout_cycles;
assign cfg_stream_velocity_high_limit = request_timeout_cycles;
assign cfg_geometry_format_selector = geometry_format_selector;
assign cfg_fault_clear = fault_clear;
assign cfg_mode_select_fallback_when_valid = mode_select_fallback_when_valid;
assign request_arm = host_cfg_valid & ~host_cfg_write;
assign host_cfg_ready = host_cfg_valid;
assign host_cfg_rdata = host_cfg_rdata_i;
assign host_cfg_rvalid = host_cfg_rvalid_i;

domino_cfg_supervisor u_domino_cfg_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .host_cfg_valid(host_cfg_valid),
    .host_cfg_write(host_cfg_write),
    .host_cfg_addr(host_cfg_addr),
    .host_cfg_wdata(host_cfg_wdata),
    .host_cfg_ready(host_cfg_ready),
    .host_cfg_rdata(host_cfg_rdata_i),
    .host_cfg_rvalid(host_cfg_rvalid_i),
    .cfg_enable(),
    .cfg_freshness_timeout_cycles(),
    .cfg_request_timeout_cycles(),
    .cfg_actuator_min_limit(),
    .cfg_actuator_max_limit(),
    .cfg_safe_fallback_command_value(),
    .cfg_stream_velocity_low_limit(),
    .cfg_stream_velocity_high_limit(),
    .cfg_geometry_format_selector(),
    .cfg_fault_clear(),
    .cfg_mode_select_fallback_when_valid(),
    .cfg_fault(),
    .cfg_defaults_loaded(1'b1)
);

domino_input_supervisor u_domino_input_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_stream_velocity_low_limit(cfg_stream_velocity_low_limit),
    .cfg_stream_velocity_high_limit(cfg_stream_velocity_high_limit),
    .cfg_geometry_format_selector(cfg_geometry_format_selector),
    .stream_velocity_mps(stream_velocity_mps),
    .flow_update_strobe(flow_update_strobe),
    .geometry_update_strobe(geometry_update_strobe),
    .geometry_format_selector(geometry_format_selector),
    .geometry_metadata_valid(geometry_metadata_valid),
    .geometry_metadata_tag(geometry_metadata_tag),
    .geometry_handle_in(geometry_handle_in),
    .geometry_reference_is_driaverml_stl(geometry_reference_is_driaverml_stl),
    .flow_epoch(flow_epoch),
    .geometry_epoch(geometry_epoch),
    .active_epoch(active_epoch),
    .validated_stream_velocity_mps(validated_stream_velocity_mps),
    .geometry_handle_canonical(geometry_handle_canonical),
    .geometry_valid(geometry_valid),
    .flow_valid(flow_valid),
    .geometry_fault(geometry_fault),
    .flow_fault(flow_fault),
    .envelope_in_range(envelope_in_range),
    .input_update_strobe(input_update_strobe)
);

domino_model_request_manager u_domino_model_request_manager (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_request_timeout_cycles(cfg_request_timeout_cycles),
    .validated_stream_velocity_mps(validated_stream_velocity_mps),
    .geometry_handle_canonical(geometry_handle_canonical),
    .active_epoch(active_epoch),
    .geometry_valid(geometry_valid),
    .flow_valid(flow_valid),
    .envelope_in_range(envelope_in_range),
    .cfg_fault(cfg_fault),
    .geometry_fault(geometry_fault),
    .flow_fault(flow_fault),
    .model_req_ready(model_req_ready),
    .request_arm(request_arm),
    .model_req_valid(model_req_valid),
    .model_req_id(model_req_id),
    .model_req_epoch(model_req_epoch),
    .model_req_geometry_handle(model_req_geometry_handle),
    .model_req_stream_velocity_mps(model_req_stream_velocity_mps),
    .model_req_timeout_cycles(model_req_timeout_cycles),
    .request_outstanding(request_outstanding),
    .request_timeout_fault(request_timeout_fault),
    .last_issued_req_id(last_issued_req_id)
);

domino_model_response_validator u_domino_model_response_validator (
    .clk(clk),
    .rst_n(rst_n),
    .request_outstanding(request_outstanding),
    .last_issued_req_id(last_issued_req_id),
    .active_epoch(active_epoch),
    .request_timeout_fault(request_timeout_fault),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_id(model_rsp_id),
    .model_rsp_epoch(model_rsp_epoch),
    .model_rsp_status_valid(model_rsp_status_valid),
    .model_rsp_status_unavailable(model_rsp_status_unavailable),
    .model_rsp_drag_force(model_rsp_drag_force),
    .model_rsp_lift_force(model_rsp_lift_force),
    .model_rsp_surface_pressure(model_rsp_surface_pressure),
    .model_rsp_flow_field_meta(model_rsp_flow_field_meta),
    .validated_response_valid(validated_response_valid),
    .validated_rsp_id(validated_rsp_id),
    .validated_rsp_epoch(validated_rsp_epoch),
    .response_mismatch_fault(response_mismatch_fault),
    .stale_response_fault(stale_response_fault),
    .model_unavailable_fault(model_unavailable_fault),
    .last_accepted_rsp_id(status_last_accepted_rsp_id),
    .validated_model_intent(validated_model_intent),
    .validated_model_intent_valid(validated_model_intent_valid),
    .stale_status(stale_status)
);

domino_actuator_command_manager u_domino_actuator_command_manager (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_actuator_min_limit(cfg_actuator_min_limit),
    .cfg_actuator_max_limit(cfg_actuator_max_limit),
    .cfg_safe_fallback_command_value(cfg_safe_fallback_command_value),
    .cfg_mode_select_fallback_when_valid(cfg_mode_select_fallback_when_valid),
    .cfg_fault(cfg_fault),
    .geometry_fault(geometry_fault),
    .flow_fault(flow_fault),
    .request_timeout_fault(request_timeout_fault),
    .stale_response_fault(stale_response_fault),
    .response_mismatch_fault(response_mismatch_fault),
    .model_unavailable_fault(model_unavailable_fault),
    .validated_model_intent(validated_model_intent),
    .validated_model_intent_valid(validated_model_intent_valid),
    .validated_response_valid(validated_response_valid),
    .safe_fallback_request(cfg_fault_clear),
    .actuator_cmd_valid(actuator_cmd_valid),
    .actuator_cmd(actuator_cmd),
    .actuator_cmd_safe_fallback(actuator_cmd_safe_fallback),
    .cmd_clamped(cmd_clamped),
    .status_mode_fallback(status_mode_fallback),
    .status_mode_model(status_mode_model),
    .status_faulted(status_faulted),
    .status_actuator_saturation_fault(status_actuator_saturation_fault),
    .last_clamped(telemetry_last_clamped_i),
    .last_fallback(telemetry_last_fallback_i)
);

domino_telemetry_fabric u_domino_telemetry_fabric (
    .clk(clk),
    .rst_n(rst_n),
    .telemetry_ready(telemetry_ready),
    .status_mode_fallback(status_mode_fallback),
    .status_mode_model(status_mode_model),
    .status_faulted(status_faulted),
    .status_stale_rejected(status_stale_rejected),
    .status_req_id(last_issued_req_id),
    .status_rsp_id(validated_rsp_id),
    .status_cfg_fault(cfg_fault),
    .status_geometry_fault(geometry_fault),
    .status_flow_fault(flow_fault),
    .status_request_timeout_fault(request_timeout_fault),
    .status_stale_response_fault(stale_response_fault),
    .status_response_mismatch_fault(response_mismatch_fault),
    .status_model_unavailable_fault(model_unavailable_fault),
    .status_actuator_saturation_fault(status_actuator_saturation_fault),
    .cmd_clamped(cmd_clamped),
    .actuator_cmd_safe_fallback(actuator_cmd_safe_fallback),
    .telemetry_valid(telemetry_valid),
    .telemetry_mode(telemetry_mode),
    .telemetry_fault_bits(telemetry_fault_bits),
    .telemetry_stale(telemetry_stale),
    .telemetry_req_id(telemetry_req_id),
    .telemetry_rsp_id(telemetry_rsp_id),
    .telemetry_last_clamped(telemetry_last_clamped),
    .telemetry_last_fallback(telemetry_last_fallback)
);

assign status_req_id = last_issued_req_id;
assign status_rsp_id = validated_rsp_id;
assign status_last_accepted_req_id = last_issued_req_id;
assign status_stale_rejected = stale_status;

endmodule
