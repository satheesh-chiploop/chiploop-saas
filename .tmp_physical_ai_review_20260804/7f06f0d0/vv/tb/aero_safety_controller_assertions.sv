/*
 * Auto-generated SVA scaffold.
 * Derived from spec_json / digital_spec_json.
 * No hardcoded design-specific signal assumptions.
 */

module aero_safety_controller_assertions (
  input logic actuator_cmd_enable,
  input logic actuator_cmd_fallback_active,
  input logic [15:0] actuator_cmd_position,
  input logic [15:0] actuator_cmd_seq,
  input logic actuator_cmd_valid,
  input logic [15:0] aero_command_sanitizer_cfg_actuator_max_limit,
  input logic [15:0] aero_command_sanitizer_cfg_actuator_min_limit,
  input logic [15:0] aero_command_sanitizer_cfg_actuator_safe_position,
  input logic aero_command_sanitizer_cfg_enable,
  input logic [15:0] aero_command_sanitizer_cfg_max_slew_rate,
  input logic aero_command_sanitizer_clamp_applied,
  input logic aero_command_sanitizer_clamp_event_pulse,
  input logic aero_command_sanitizer_cmd_enable,
  input logic [15:0] aero_command_sanitizer_cmd_position,
  input logic [15:0] aero_command_sanitizer_cmd_seq,
  input logic aero_command_sanitizer_cmd_valid,
  input logic aero_command_sanitizer_fallback_active_in,
  input logic aero_command_sanitizer_fallback_active_out,
  input logic aero_command_sanitizer_fault_active_in,
  input logic [15:0] aero_command_sanitizer_req_seq,
  input logic [15:0] aero_command_sanitizer_rsp_drag_force,
  input logic [15:0] aero_command_sanitizer_rsp_flow_field,
  input logic [15:0] aero_command_sanitizer_rsp_lift_force,
  input logic [15:0] aero_command_sanitizer_rsp_seq,
  input logic [15:0] aero_command_sanitizer_rsp_surface_pressure,
  input logic aero_command_sanitizer_rsp_valid,
  input logic [15:0] aero_command_sanitizer_safe_position_source,
  input logic [15:0] aero_command_sanitizer_sanitized_position,
  input logic [15:0] aero_regfile_cfg_actuator_max_limit,
  input logic [15:0] aero_regfile_cfg_actuator_min_limit,
  input logic [15:0] aero_regfile_cfg_actuator_safe_position,
  input logic aero_regfile_cfg_clear_faults,
  input logic [15:0] aero_regfile_cfg_command_timeout_cycles,
  input logic aero_regfile_cfg_enable,
  input logic [7:0] aero_regfile_cfg_geometry_format_id,
  input logic [7:0] aero_regfile_cfg_geometry_source_id,
  input logic [15:0] aero_regfile_cfg_geometry_version,
  input logic [15:0] aero_regfile_cfg_max_slew_rate,
  input logic [15:0] aero_regfile_cfg_stream_velocity_mps_setpoint,
  input logic [15:0] aero_regfile_cfg_velocity_max_limit,
  input logic [15:0] aero_regfile_cfg_velocity_min_limit,
  input logic [15:0] aero_regfile_status_clamp_event_count,
  input logic [3:0] aero_regfile_status_current_state,
  input logic aero_regfile_status_fallback_active,
  input logic [15:0] aero_regfile_status_last_accepted_seq,
  input logic [3:0] aero_regfile_status_last_fault_code,
  input logic [15:0] aero_regfile_status_last_response_age,
  input logic aero_regfile_status_model_response_valid_seen,
  input logic aero_regfile_status_request_inflight,
  input logic [15:0] aero_regfile_status_stale_reject_count,
  input logic [15:0] aero_supervisor_cfg_actuator_max_limit,
  input logic [15:0] aero_supervisor_cfg_actuator_min_limit,
  input logic [15:0] aero_supervisor_cfg_actuator_safe_position,
  input logic aero_supervisor_cfg_clear_faults,
  input logic [15:0] aero_supervisor_cfg_command_timeout_cycles,
  input logic aero_supervisor_cfg_enable,
  input logic [7:0] aero_supervisor_cfg_geometry_format_id,
  input logic [7:0] aero_supervisor_cfg_geometry_source_id,
  input logic [15:0] aero_supervisor_cfg_geometry_version,
  input logic [15:0] aero_supervisor_cfg_max_slew_rate,
  input logic [15:0] aero_supervisor_cfg_stream_velocity_mps_setpoint,
  input logic [15:0] aero_supervisor_cfg_velocity_max_limit,
  input logic [15:0] aero_supervisor_cfg_velocity_min_limit,
  input logic [3:0] aero_supervisor_fault_code,
  input logic aero_supervisor_geometry_invalid,
  input logic aero_supervisor_out_of_range_fault,
  input logic aero_supervisor_protocol_error_fault,
  input logic aero_supervisor_req_inflight,
  input logic aero_supervisor_req_ready,
  input logic [15:0] aero_supervisor_req_seq,
  input logic aero_supervisor_req_valid,
  input logic [15:0] aero_supervisor_request_age_cycles,
  input logic aero_supervisor_request_stale,
  input logic [15:0] aero_supervisor_rsp_drag_force,
  input logic [15:0] aero_supervisor_rsp_flow_field,
  input logic aero_supervisor_rsp_inference_status_not_executed,
  input logic [15:0] aero_supervisor_rsp_lift_force,
  input logic [15:0] aero_supervisor_rsp_seq,
  input logic [15:0] aero_supervisor_rsp_surface_pressure,
  input logic aero_supervisor_rsp_valid,
  input logic aero_supervisor_sequence_mismatch_fault,
  input logic aero_supervisor_service_unavailable_fault,
  input logic aero_supervisor_stale_response_fault,
  input logic [15:0] clamp_event_count,
  input logic clk,
  input logic [3:0] current_state,
  input logic [15:0] debug_seq_trace,
  input logic [15:0] debug_timeout_age,
  input logic fallback_active,
  input logic [7:0] geom_format_id_in,
  input logic [7:0] geom_source_id_in,
  input logic geom_valid,
  input logic [15:0] geom_version_in,
  input logic [7:0] host_reg_addr,
  input logic host_reg_rd_valid,
  input logic [31:0] host_reg_rdata,
  input logic host_reg_ready,
  input logic host_reg_rvalid,
  input logic [31:0] host_reg_wdata,
  input logic host_reg_wr_valid,
  input logic [15:0] last_accepted_seq,
  input logic [3:0] last_fault_code,
  input logic [15:0] last_response_age,
  input logic [15:0] model_req_actuator_max_limit,
  input logic [15:0] model_req_actuator_min_limit,
  input logic [15:0] model_req_actuator_safe_position,
  input logic [15:0] model_req_command_timeout_cycles,
  input logic model_req_enable,
  input logic [15:0] model_req_flow_velocity_mps,
  input logic model_req_geom_valid,
  input logic [7:0] model_req_geometry_format_id,
  input logic [7:0] model_req_geometry_source_id,
  input logic [15:0] model_req_geometry_version,
  input logic [15:0] model_req_max_slew_rate,
  input logic model_req_ready,
  input logic [15:0] model_req_seq,
  input logic [15:0] model_req_stream_velocity_mps,
  input logic model_req_valid,
  input logic [15:0] model_req_velocity_max_limit,
  input logic [15:0] model_req_velocity_min_limit,
  input logic model_response_valid_seen,
  input logic [15:0] model_rsp_drag_force,
  input logic [15:0] model_rsp_flow_field,
  input logic model_rsp_inference_status_not_executed,
  input logic [15:0] model_rsp_lift_force,
  input logic [15:0] model_rsp_seq,
  input logic [15:0] model_rsp_surface_pressure,
  input logic model_rsp_valid,
  input logic request_inflight,
  input logic rst_n,
  input logic [15:0] stale_reject_count,
  input logic [15:0] stream_velocity_mps,
  input logic tick_1ms
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(rst_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $error("Reset signal has X/Z state.");
  property p_host_reg_ready_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_reg_ready);
  endproperty

  a_host_reg_ready_known_after_reset: assert property(p_host_reg_ready_known_after_reset)
    else $error("Signal host_reg_ready has X/Z after reset release.");
  property p_host_reg_rdata_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_reg_rdata);
  endproperty

  a_host_reg_rdata_known_after_reset: assert property(p_host_reg_rdata_known_after_reset)
    else $error("Signal host_reg_rdata has X/Z after reset release.");
  property p_host_reg_rvalid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_reg_rvalid);
  endproperty

  a_host_reg_rvalid_known_after_reset: assert property(p_host_reg_rvalid_known_after_reset)
    else $error("Signal host_reg_rvalid has X/Z after reset release.");
  property p_model_req_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_valid);
  endproperty

  a_model_req_valid_known_after_reset: assert property(p_model_req_valid_known_after_reset)
    else $error("Signal model_req_valid has X/Z after reset release.");
  property p_model_req_seq_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_seq);
  endproperty

  a_model_req_seq_known_after_reset: assert property(p_model_req_seq_known_after_reset)
    else $error("Signal model_req_seq has X/Z after reset release.");
  property p_model_req_enable_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_enable);
  endproperty

  a_model_req_enable_known_after_reset: assert property(p_model_req_enable_known_after_reset)
    else $error("Signal model_req_enable has X/Z after reset release.");
  property p_model_req_stream_velocity_mps_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_stream_velocity_mps);
  endproperty

  a_model_req_stream_velocity_mps_known_after_reset: assert property(p_model_req_stream_velocity_mps_known_after_reset)
    else $error("Signal model_req_stream_velocity_mps has X/Z after reset release.");
  property p_model_req_velocity_min_limit_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_velocity_min_limit);
  endproperty

  a_model_req_velocity_min_limit_known_after_reset: assert property(p_model_req_velocity_min_limit_known_after_reset)
    else $error("Signal model_req_velocity_min_limit has X/Z after reset release.");
  property p_model_req_velocity_max_limit_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_velocity_max_limit);
  endproperty

  a_model_req_velocity_max_limit_known_after_reset: assert property(p_model_req_velocity_max_limit_known_after_reset)
    else $error("Signal model_req_velocity_max_limit has X/Z after reset release.");
  property p_model_req_actuator_min_limit_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_actuator_min_limit);
  endproperty

  a_model_req_actuator_min_limit_known_after_reset: assert property(p_model_req_actuator_min_limit_known_after_reset)
    else $error("Signal model_req_actuator_min_limit has X/Z after reset release.");
  property p_model_req_actuator_max_limit_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_actuator_max_limit);
  endproperty

  a_model_req_actuator_max_limit_known_after_reset: assert property(p_model_req_actuator_max_limit_known_after_reset)
    else $error("Signal model_req_actuator_max_limit has X/Z after reset release.");
  property p_model_req_actuator_safe_position_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_actuator_safe_position);
  endproperty

  a_model_req_actuator_safe_position_known_after_reset: assert property(p_model_req_actuator_safe_position_known_after_reset)
    else $error("Signal model_req_actuator_safe_position has X/Z after reset release.");

endmodule
