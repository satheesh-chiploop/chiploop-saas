module aero_safety_controller(
    clk,
    rst_n,
    tick_1ms,
    host_reg_wr_valid,
    host_reg_rd_valid,
    host_reg_ready,
    host_reg_addr,
    host_reg_wdata,
    host_reg_rdata,
    host_reg_rvalid,
    stream_velocity_mps,
    geom_valid,
    geom_format_id_in,
    geom_source_id_in,
    geom_version_in,
    model_req_valid,
    model_req_ready,
    model_req_seq,
    model_req_enable,
    model_req_stream_velocity_mps,
    model_req_velocity_min_limit,
    model_req_velocity_max_limit,
    model_req_actuator_min_limit,
    model_req_actuator_max_limit,
    model_req_actuator_safe_position,
    model_req_command_timeout_cycles,
    model_req_max_slew_rate,
    model_req_geometry_format_id,
    model_req_geometry_source_id,
    model_req_geometry_version,
    model_req_flow_velocity_mps,
    model_req_geom_valid,
    model_rsp_valid,
    model_rsp_seq,
    model_rsp_drag_force,
    model_rsp_lift_force,
    model_rsp_surface_pressure,
    model_rsp_flow_field,
    model_rsp_inference_status_not_executed,
    actuator_cmd_valid,
    actuator_cmd_enable,
    actuator_cmd_position,
    actuator_cmd_seq,
    actuator_cmd_fallback_active,
    current_state,
    last_fault_code,
    stale_reject_count,
    clamp_event_count,
    fallback_active,
    last_accepted_seq,
    last_response_age,
    request_inflight,
    model_response_valid_seen,
    debug_seq_trace,
    debug_timeout_age,
    aero_regfile_cfg_enable,
    aero_regfile_cfg_stream_velocity_mps_setpoint,
    aero_regfile_cfg_velocity_min_limit,
    aero_regfile_cfg_velocity_max_limit,
    aero_regfile_cfg_actuator_min_limit,
    aero_regfile_cfg_actuator_max_limit,
    aero_regfile_cfg_actuator_safe_position,
    aero_regfile_cfg_command_timeout_cycles,
    aero_regfile_cfg_max_slew_rate,
    aero_regfile_cfg_geometry_format_id,
    aero_regfile_cfg_geometry_source_id,
    aero_regfile_cfg_geometry_version,
    aero_regfile_cfg_clear_faults,
    aero_regfile_status_current_state,
    aero_regfile_status_last_fault_code,
    aero_regfile_status_stale_reject_count,
    aero_regfile_status_clamp_event_count,
    aero_regfile_status_fallback_active,
    aero_regfile_status_last_accepted_seq,
    aero_regfile_status_last_response_age,
    aero_regfile_status_request_inflight,
    aero_regfile_status_model_response_valid_seen,
    aero_supervisor_cfg_enable,
    aero_supervisor_cfg_stream_velocity_mps_setpoint,
    aero_supervisor_cfg_velocity_min_limit,
    aero_supervisor_cfg_velocity_max_limit,
    aero_supervisor_cfg_actuator_min_limit,
    aero_supervisor_cfg_actuator_max_limit,
    aero_supervisor_cfg_actuator_safe_position,
    aero_supervisor_cfg_command_timeout_cycles,
    aero_supervisor_cfg_max_slew_rate,
    aero_supervisor_cfg_geometry_format_id,
    aero_supervisor_cfg_geometry_source_id,
    aero_supervisor_cfg_geometry_version,
    aero_supervisor_cfg_clear_faults,
    aero_supervisor_req_ready,
    aero_supervisor_rsp_valid,
    aero_supervisor_rsp_seq,
    aero_supervisor_rsp_drag_force,
    aero_supervisor_rsp_lift_force,
    aero_supervisor_rsp_surface_pressure,
    aero_supervisor_rsp_flow_field,
    aero_supervisor_rsp_inference_status_not_executed,
    aero_supervisor_req_valid,
    aero_supervisor_req_seq,
    aero_supervisor_req_inflight,
    aero_supervisor_fault_code,
    aero_supervisor_request_age_cycles,
    aero_supervisor_request_stale,
    aero_supervisor_geometry_invalid,
    aero_supervisor_out_of_range_fault,
    aero_supervisor_sequence_mismatch_fault,
    aero_supervisor_service_unavailable_fault,
    aero_supervisor_protocol_error_fault,
    aero_supervisor_stale_response_fault,
    aero_command_sanitizer_cfg_actuator_min_limit,
    aero_command_sanitizer_cfg_actuator_max_limit,
    aero_command_sanitizer_cfg_actuator_safe_position,
    aero_command_sanitizer_cfg_max_slew_rate,
    aero_command_sanitizer_cfg_enable,
    aero_command_sanitizer_fallback_active_in,
    aero_command_sanitizer_fault_active_in,
    aero_command_sanitizer_req_seq,
    aero_command_sanitizer_rsp_valid,
    aero_command_sanitizer_rsp_seq,
    aero_command_sanitizer_rsp_drag_force,
    aero_command_sanitizer_rsp_lift_force,
    aero_command_sanitizer_rsp_surface_pressure,
    aero_command_sanitizer_rsp_flow_field,
    aero_command_sanitizer_safe_position_source,
    aero_command_sanitizer_cmd_position,
    aero_command_sanitizer_cmd_valid,
    aero_command_sanitizer_cmd_enable,
    aero_command_sanitizer_cmd_seq,
    aero_command_sanitizer_fallback_active_out,
    aero_command_sanitizer_clamp_applied,
    aero_command_sanitizer_clamp_event_pulse,
    aero_command_sanitizer_sanitized_position
);
input clk;
input rst_n;
input tick_1ms;
input host_reg_wr_valid;
input host_reg_rd_valid;
output host_reg_ready;
input [7:0] host_reg_addr;
input [31:0] host_reg_wdata;
output [31:0] host_reg_rdata;
output host_reg_rvalid;
input [15:0] stream_velocity_mps;
input geom_valid;
input [7:0] geom_format_id_in;
input [7:0] geom_source_id_in;
input [15:0] geom_version_in;
output model_req_valid;
input model_req_ready;
output [15:0] model_req_seq;
output model_req_enable;
output [15:0] model_req_stream_velocity_mps;
output [15:0] model_req_velocity_min_limit;
output [15:0] model_req_velocity_max_limit;
output [15:0] model_req_actuator_min_limit;
output [15:0] model_req_actuator_max_limit;
output [15:0] model_req_actuator_safe_position;
output [15:0] model_req_command_timeout_cycles;
output [15:0] model_req_max_slew_rate;
output [7:0] model_req_geometry_format_id;
output [7:0] model_req_geometry_source_id;
output [15:0] model_req_geometry_version;
output [15:0] model_req_flow_velocity_mps;
output model_req_geom_valid;
input model_rsp_valid;
input [15:0] model_rsp_seq;
input [15:0] model_rsp_drag_force;
input [15:0] model_rsp_lift_force;
input [15:0] model_rsp_surface_pressure;
input [15:0] model_rsp_flow_field;
input model_rsp_inference_status_not_executed;
output actuator_cmd_valid;
output actuator_cmd_enable;
output [15:0] actuator_cmd_position;
output [15:0] actuator_cmd_seq;
output actuator_cmd_fallback_active;
output [3:0] current_state;
output [3:0] last_fault_code;
output [15:0] stale_reject_count;
output [15:0] clamp_event_count;
output fallback_active;
output [15:0] last_accepted_seq;
output [15:0] last_response_age;
output request_inflight;
output model_response_valid_seen;
output [15:0] debug_seq_trace;
output [15:0] debug_timeout_age;
input aero_regfile_cfg_enable;
input [15:0] aero_regfile_cfg_stream_velocity_mps_setpoint;
input [15:0] aero_regfile_cfg_velocity_min_limit;
input [15:0] aero_regfile_cfg_velocity_max_limit;
input [15:0] aero_regfile_cfg_actuator_min_limit;
input [15:0] aero_regfile_cfg_actuator_max_limit;
input [15:0] aero_regfile_cfg_actuator_safe_position;
input [15:0] aero_regfile_cfg_command_timeout_cycles;
input [15:0] aero_regfile_cfg_max_slew_rate;
input [7:0] aero_regfile_cfg_geometry_format_id;
input [7:0] aero_regfile_cfg_geometry_source_id;
input [15:0] aero_regfile_cfg_geometry_version;
input aero_regfile_cfg_clear_faults;
output [3:0] aero_regfile_status_current_state;
output [3:0] aero_regfile_status_last_fault_code;
output [15:0] aero_regfile_status_stale_reject_count;
output [15:0] aero_regfile_status_clamp_event_count;
output aero_regfile_status_fallback_active;
output [15:0] aero_regfile_status_last_accepted_seq;
output [15:0] aero_regfile_status_last_response_age;
output aero_regfile_status_request_inflight;
output aero_regfile_status_model_response_valid_seen;
output aero_supervisor_cfg_enable;
output [15:0] aero_supervisor_cfg_stream_velocity_mps_setpoint;
output [15:0] aero_supervisor_cfg_velocity_min_limit;
output [15:0] aero_supervisor_cfg_velocity_max_limit;
output [15:0] aero_supervisor_cfg_actuator_min_limit;
output [15:0] aero_supervisor_cfg_actuator_max_limit;
output [15:0] aero_supervisor_cfg_actuator_safe_position;
output [15:0] aero_supervisor_cfg_command_timeout_cycles;
output [15:0] aero_supervisor_cfg_max_slew_rate;
output [7:0] aero_supervisor_cfg_geometry_format_id;
output [7:0] aero_supervisor_cfg_geometry_source_id;
output [15:0] aero_supervisor_cfg_geometry_version;
output aero_supervisor_cfg_clear_faults;
output aero_supervisor_req_ready;
output aero_supervisor_rsp_valid;
output [15:0] aero_supervisor_rsp_seq;
output [15:0] aero_supervisor_rsp_drag_force;
output [15:0] aero_supervisor_rsp_lift_force;
output [15:0] aero_supervisor_rsp_surface_pressure;
output [15:0] aero_supervisor_rsp_flow_field;
output aero_supervisor_rsp_inference_status_not_executed;
input aero_supervisor_req_valid;
input [15:0] aero_supervisor_req_seq;
input aero_supervisor_req_inflight;
input [3:0] aero_supervisor_fault_code;
input [15:0] aero_supervisor_request_age_cycles;
input aero_supervisor_request_stale;
input aero_supervisor_geometry_invalid;
input aero_supervisor_out_of_range_fault;
input aero_supervisor_sequence_mismatch_fault;
input aero_supervisor_service_unavailable_fault;
input aero_supervisor_protocol_error_fault;
input aero_supervisor_stale_response_fault;
output [15:0] aero_command_sanitizer_cfg_actuator_min_limit;
output [15:0] aero_command_sanitizer_cfg_actuator_max_limit;
output [15:0] aero_command_sanitizer_cfg_actuator_safe_position;
output [15:0] aero_command_sanitizer_cfg_max_slew_rate;
output aero_command_sanitizer_cfg_enable;
output aero_command_sanitizer_fallback_active_in;
output aero_command_sanitizer_fault_active_in;
output [15:0] aero_command_sanitizer_req_seq;
output aero_command_sanitizer_rsp_valid;
output [15:0] aero_command_sanitizer_rsp_seq;
output [15:0] aero_command_sanitizer_rsp_drag_force;
output [15:0] aero_command_sanitizer_rsp_lift_force;
output [15:0] aero_command_sanitizer_rsp_surface_pressure;
output [15:0] aero_command_sanitizer_rsp_flow_field;
output [15:0] aero_command_sanitizer_safe_position_source;
input [15:0] aero_command_sanitizer_cmd_position;
input aero_command_sanitizer_cmd_valid;
input aero_command_sanitizer_cmd_enable;
input [15:0] aero_command_sanitizer_cmd_seq;
input aero_command_sanitizer_fallback_active_out;
input aero_command_sanitizer_clamp_applied;
input aero_command_sanitizer_clamp_event_pulse;
input [15:0] aero_command_sanitizer_sanitized_position;
wire host_reg_ready_w;
wire [31:0] host_reg_rdata_w;
wire host_reg_rvalid_w;
wire aero_regfile_cfg_enable_w;
wire [15:0] aero_regfile_cfg_stream_velocity_mps_setpoint_w;
wire [15:0] aero_regfile_cfg_velocity_min_limit_w;
wire [15:0] aero_regfile_cfg_velocity_max_limit_w;
wire [15:0] aero_regfile_cfg_actuator_min_limit_w;
wire [15:0] aero_regfile_cfg_actuator_max_limit_w;
wire [15:0] aero_regfile_cfg_actuator_safe_position_w;
wire [15:0] aero_regfile_cfg_command_timeout_cycles_w;
wire [15:0] aero_regfile_cfg_max_slew_rate_w;
wire [7:0] aero_regfile_cfg_geometry_format_id_w;
wire [7:0] aero_regfile_cfg_geometry_source_id_w;
wire [15:0] aero_regfile_cfg_geometry_version_w;
wire aero_regfile_cfg_clear_faults_w;
wire [3:0] aero_regfile_status_current_state_w;
wire [3:0] aero_regfile_status_last_fault_code_w;
wire [15:0] aero_regfile_status_stale_reject_count_w;
wire [15:0] aero_regfile_status_clamp_event_count_w;
wire aero_regfile_status_fallback_active_w;
wire [15:0] aero_regfile_status_last_accepted_seq_w;
wire [15:0] aero_regfile_status_last_response_age_w;
wire aero_regfile_status_request_inflight_w;
wire aero_regfile_status_model_response_valid_seen_w;
wire aero_supervisor_req_valid_w;
wire [15:0] aero_supervisor_req_seq_w;
wire aero_supervisor_req_inflight_w;
wire [3:0] aero_supervisor_fault_code_w;
wire [15:0] aero_supervisor_request_age_cycles_w;
wire aero_supervisor_request_stale_w;
wire aero_supervisor_geometry_invalid_w;
wire aero_supervisor_out_of_range_fault_w;
wire aero_supervisor_sequence_mismatch_fault_w;
wire aero_supervisor_service_unavailable_fault_w;
wire aero_supervisor_protocol_error_fault_w;
wire aero_supervisor_stale_response_fault_w;
wire [15:0] aero_command_sanitizer_cmd_position_w;
wire aero_command_sanitizer_cmd_valid_w;
wire aero_command_sanitizer_cmd_enable_w;
wire [15:0] aero_command_sanitizer_cmd_seq_w;
wire aero_command_sanitizer_fallback_active_out_w;
wire aero_command_sanitizer_clamp_applied_w;
wire aero_command_sanitizer_clamp_event_pulse_w;
wire [15:0] aero_command_sanitizer_sanitized_position_w;
assign host_reg_ready = host_reg_ready_w;
assign host_reg_rdata = host_reg_rdata_w;
assign host_reg_rvalid = host_reg_rvalid_w;
assign model_req_valid = aero_supervisor_req_valid_w;
assign model_req_seq = aero_supervisor_req_seq_w;
assign model_req_enable = aero_regfile_cfg_enable_w;
assign model_req_stream_velocity_mps = aero_regfile_cfg_stream_velocity_mps_setpoint_w;
assign model_req_velocity_min_limit = aero_regfile_cfg_velocity_min_limit_w;
assign model_req_velocity_max_limit = aero_regfile_cfg_velocity_max_limit_w;
assign model_req_actuator_min_limit = aero_regfile_cfg_actuator_min_limit_w;
assign model_req_actuator_max_limit = aero_regfile_cfg_actuator_max_limit_w;
assign model_req_actuator_safe_position = aero_regfile_cfg_actuator_safe_position_w;
assign model_req_command_timeout_cycles = aero_regfile_cfg_command_timeout_cycles_w;
assign model_req_max_slew_rate = aero_regfile_cfg_max_slew_rate_w;
assign model_req_geometry_format_id = aero_regfile_cfg_geometry_format_id_w;
assign model_req_geometry_source_id = aero_regfile_cfg_geometry_source_id_w;
assign model_req_geometry_version = aero_regfile_cfg_geometry_version_w;
assign model_req_flow_velocity_mps = stream_velocity_mps;
assign model_req_geom_valid = geom_valid;
assign aero_regfile_status_current_state_w = current_state;
assign aero_regfile_status_last_fault_code_w = last_fault_code;
assign aero_regfile_status_stale_reject_count_w = stale_reject_count;
assign aero_regfile_status_clamp_event_count_w = clamp_event_count;
assign aero_regfile_status_fallback_active_w = fallback_active;
assign aero_regfile_status_last_accepted_seq_w = last_accepted_seq;
assign aero_regfile_status_last_response_age_w = last_response_age;
assign aero_regfile_status_request_inflight_w = request_inflight;
assign aero_regfile_status_model_response_valid_seen_w = model_response_valid_seen;
assign aero_supervisor_cfg_enable = aero_regfile_cfg_enable_w;
assign aero_supervisor_cfg_stream_velocity_mps_setpoint = aero_regfile_cfg_stream_velocity_mps_setpoint_w;
assign aero_supervisor_cfg_velocity_min_limit = aero_regfile_cfg_velocity_min_limit_w;
assign aero_supervisor_cfg_velocity_max_limit = aero_regfile_cfg_velocity_max_limit_w;
assign aero_supervisor_cfg_actuator_min_limit = aero_regfile_cfg_actuator_min_limit_w;
assign aero_supervisor_cfg_actuator_max_limit = aero_regfile_cfg_actuator_max_limit_w;
assign aero_supervisor_cfg_actuator_safe_position = aero_regfile_cfg_actuator_safe_position_w;
assign aero_supervisor_cfg_command_timeout_cycles = aero_regfile_cfg_command_timeout_cycles_w;
assign aero_supervisor_cfg_max_slew_rate = aero_regfile_cfg_max_slew_rate_w;
assign aero_supervisor_cfg_geometry_format_id = aero_regfile_cfg_geometry_format_id_w;
assign aero_supervisor_cfg_geometry_source_id = aero_regfile_cfg_geometry_source_id_w;
assign aero_supervisor_cfg_geometry_version = aero_regfile_cfg_geometry_version_w;
assign aero_supervisor_cfg_clear_faults = aero_regfile_cfg_clear_faults_w;
assign aero_supervisor_req_ready = model_req_ready;
assign aero_supervisor_rsp_valid = model_rsp_valid;
assign aero_supervisor_rsp_seq = model_rsp_seq;
assign aero_supervisor_rsp_drag_force = model_rsp_drag_force;
assign aero_supervisor_rsp_lift_force = model_rsp_lift_force;
assign aero_supervisor_rsp_surface_pressure = model_rsp_surface_pressure;
assign aero_supervisor_rsp_flow_field = model_rsp_flow_field;
assign aero_supervisor_rsp_inference_status_not_executed = model_rsp_inference_status_not_executed;
assign aero_command_sanitizer_cfg_actuator_min_limit = aero_regfile_cfg_actuator_min_limit_w;
assign aero_command_sanitizer_cfg_actuator_max_limit = aero_regfile_cfg_actuator_max_limit_w;
assign aero_command_sanitizer_cfg_actuator_safe_position = aero_regfile_cfg_actuator_safe_position_w;
assign aero_command_sanitizer_cfg_max_slew_rate = aero_regfile_cfg_max_slew_rate_w;
assign aero_command_sanitizer_cfg_enable = aero_regfile_cfg_enable_w;
assign aero_command_sanitizer_fallback_active_in = fallback_active;
assign aero_command_sanitizer_fault_active_in = (last_fault_code != 4'd0);
assign aero_command_sanitizer_req_seq = last_accepted_seq;
assign aero_command_sanitizer_rsp_valid = model_rsp_valid;
assign aero_command_sanitizer_rsp_seq = model_rsp_seq;
assign aero_command_sanitizer_rsp_drag_force = model_rsp_drag_force;
assign aero_command_sanitizer_rsp_lift_force = model_rsp_lift_force;
assign aero_command_sanitizer_rsp_surface_pressure = model_rsp_surface_pressure;
assign aero_command_sanitizer_rsp_flow_field = model_rsp_flow_field;
assign aero_command_sanitizer_safe_position_source = aero_regfile_cfg_actuator_safe_position_w;
assign current_state = aero_supervisor.current_state;
assign last_fault_code = aero_supervisor.aero_supervisor_fault_code;
assign stale_reject_count = aero_supervisor.stale_reject_count;
assign clamp_event_count = aero_supervisor.clamp_event_count;
assign fallback_active = aero_supervisor.fallback_active;
assign last_accepted_seq = aero_supervisor.last_accepted_seq;
assign last_response_age = aero_supervisor.last_response_age;
assign request_inflight = aero_supervisor.aero_supervisor_req_inflight;
assign model_response_valid_seen = aero_supervisor.model_response_valid_seen;
assign debug_seq_trace = last_accepted_seq;
assign debug_timeout_age = last_response_age;
assign actuator_cmd_valid = aero_command_sanitizer_cmd_valid_w;
assign actuator_cmd_enable = aero_command_sanitizer_cmd_enable_w;
assign actuator_cmd_position = aero_command_sanitizer_cmd_position_w;
assign actuator_cmd_seq = aero_command_sanitizer_cmd_seq_w;
assign actuator_cmd_fallback_active = aero_command_sanitizer_fallback_active_out_w;
assign aero_regfile_cfg_enable_w = aero_regfile_cfg_enable;
assign aero_regfile_cfg_stream_velocity_mps_setpoint_w = aero_regfile_cfg_stream_velocity_mps_setpoint;
assign aero_regfile_cfg_velocity_min_limit_w = aero_regfile_cfg_velocity_min_limit;
assign aero_regfile_cfg_velocity_max_limit_w = aero_regfile_cfg_velocity_max_limit;
assign aero_regfile_cfg_actuator_min_limit_w = aero_regfile_cfg_actuator_min_limit;
assign aero_regfile_cfg_actuator_max_limit_w = aero_regfile_cfg_actuator_max_limit;
assign aero_regfile_cfg_actuator_safe_position_w = aero_regfile_cfg_actuator_safe_position;
assign aero_regfile_cfg_command_timeout_cycles_w = aero_regfile_cfg_command_timeout_cycles;
assign aero_regfile_cfg_max_slew_rate_w = aero_regfile_cfg_max_slew_rate;
assign aero_regfile_cfg_geometry_format_id_w = aero_regfile_cfg_geometry_format_id;
assign aero_regfile_cfg_geometry_source_id_w = aero_regfile_cfg_geometry_source_id;
assign aero_regfile_cfg_geometry_version_w = aero_regfile_cfg_geometry_version;
assign aero_regfile_cfg_clear_faults_w = aero_regfile_cfg_clear_faults;
assign aero_regfile_status_current_state = current_state;
assign aero_regfile_status_last_fault_code = last_fault_code;
assign aero_regfile_status_stale_reject_count = stale_reject_count;
assign aero_regfile_status_clamp_event_count = clamp_event_count;
assign aero_regfile_status_fallback_active = fallback_active;
assign aero_regfile_status_last_accepted_seq = last_accepted_seq;
assign aero_regfile_status_last_response_age = last_response_age;
assign aero_regfile_status_request_inflight = request_inflight;
assign aero_regfile_status_model_response_valid_seen = model_response_valid_seen;
assign aero_supervisor_req_valid_w = model_req_valid;
assign aero_supervisor_req_seq_w = model_req_seq;
assign aero_supervisor_req_inflight_w = request_inflight;
assign aero_supervisor_fault_code_w = last_fault_code;
assign aero_supervisor_request_age_cycles_w = debug_timeout_age;
assign aero_supervisor_request_stale_w = (last_fault_code == 4'd2);
assign aero_supervisor_geometry_invalid_w = 1'b0;
assign aero_supervisor_out_of_range_fault_w = 1'b0;
assign aero_supervisor_sequence_mismatch_fault_w = 1'b0;
assign aero_supervisor_service_unavailable_fault_w = 1'b0;
assign aero_supervisor_protocol_error_fault_w = 1'b0;
assign aero_supervisor_stale_response_fault_w = 1'b0;

wire [3:0] current_state_w;
wire [3:0] last_fault_code_w;
wire [15:0] stale_reject_count_w;
wire [15:0] clamp_event_count_w;
wire fallback_active_w;
wire [15:0] last_accepted_seq_w;
wire [15:0] last_response_age_w;
wire request_inflight_w;
wire model_response_valid_seen_w;

assign current_state = current_state_w;
assign last_fault_code = last_fault_code_w;
assign stale_reject_count = stale_reject_count_w;
assign clamp_event_count = clamp_event_count_w;
assign fallback_active = fallback_active_w;
assign last_accepted_seq = last_accepted_seq_w;
assign last_response_age = last_response_age_w;
assign request_inflight = request_inflight_w;
assign model_response_valid_seen = model_response_valid_seen_w;

aero_supervisor u_aero_supervisor(
    .clk(clk),
    .rst_n(rst_n),
    .tick_1ms(tick_1ms),
    .cfg_enable(aero_regfile_cfg_enable_w),
    .cfg_stream_velocity_mps_setpoint(aero_regfile_cfg_stream_velocity_mps_setpoint_w),
    .cfg_velocity_min_limit(aero_regfile_cfg_velocity_min_limit_w),
    .cfg_velocity_max_limit(aero_regfile_cfg_velocity_max_limit_w),
    .cfg_actuator_min_limit(aero_regfile_cfg_actuator_min_limit_w),
    .cfg_actuator_max_limit(aero_regfile_cfg_actuator_max_limit_w),
    .cfg_actuator_safe_position(aero_regfile_cfg_actuator_safe_position_w),
    .cfg_command_timeout_cycles(aero_regfile_cfg_command_timeout_cycles_w),
    .cfg_max_slew_rate(aero_regfile_cfg_max_slew_rate_w),
    .cfg_geometry_format_id(aero_regfile_cfg_geometry_format_id_w),
    .cfg_geometry_source_id(aero_regfile_cfg_geometry_source_id_w),
    .cfg_geometry_version(aero_regfile_cfg_geometry_version_w),
    .cfg_clear_faults(aero_regfile_cfg_clear_faults_w),
    .stream_velocity_mps(stream_velocity_mps),
    .geom_valid(geom_valid),
    .geom_format_id_in(geom_format_id_in),
    .geom_source_id_in(geom_source_id_in),
    .geom_version_in(geom_version_in),
    .req_ready(model_req_ready),
    .rsp_valid(model_rsp_valid),
    .rsp_seq(model_rsp_seq),
    .rsp_drag_force(model_rsp_drag_force),
    .rsp_lift_force(model_rsp_lift_force),
    .rsp_surface_pressure(model_rsp_surface_pressure),
    .rsp_flow_field(model_rsp_flow_field),
    .rsp_inference_status_not_executed(model_rsp_inference_status_not_executed),
    .req_valid(current_state_w[0]),
    .req_seq(last_accepted_seq_w),
    .req_inflight(request_inflight_w),
    .current_state(current_state_w),
    .fault_code(last_fault_code_w),
    .stale_reject_count(stale_reject_count_w),
    .clamp_event_count(clamp_event_count_w),
    .fallback_active(fallback_active_w),
    .last_accepted_seq(last_accepted_seq_w),
    .last_response_age(last_response_age_w),
    .model_response_valid_seen(model_response_valid_seen_w),
    .request_age_cycles(debug_timeout_age),
    .request_stale(),
    .geometry_invalid(),
    .out_of_range_fault(),
    .sequence_mismatch_fault(),
    .service_unavailable_fault(),
    .protocol_error_fault(),
    .stale_response_fault()
);

endmodule
