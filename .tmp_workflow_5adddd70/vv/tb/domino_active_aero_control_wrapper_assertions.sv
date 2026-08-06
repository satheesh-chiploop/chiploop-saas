/*
 * Auto-generated SVA scaffold.
 * Derived from spec_json / digital_spec_json.
 * No hardcoded design-specific signal assumptions.
 */

module domino_active_aero_control_wrapper_assertions (
  input logic [15:0] actuator_cmd,
  input logic actuator_cmd_safe_fallback,
  input logic actuator_cmd_valid,
  input logic [15:0] actuator_max_limit,
  input logic [15:0] actuator_min_limit,
  input logic clk,
  input logic cmd_clamped,
  input logic enable,
  input logic fault_clear,
  input logic flow_update_strobe,
  input logic [15:0] freshness_timeout_cycles,
  input logic [7:0] geometry_format_selector,
  input logic [31:0] geometry_handle_in,
  input logic [15:0] geometry_metadata_tag,
  input logic geometry_metadata_valid,
  input logic geometry_reference_is_driaverml_stl,
  input logic geometry_update_strobe,
  input logic [7:0] host_cfg_addr,
  input logic [31:0] host_cfg_rdata,
  input logic host_cfg_ready,
  input logic host_cfg_rvalid,
  input logic host_cfg_valid,
  input logic [31:0] host_cfg_wdata,
  input logic host_cfg_write,
  input logic mode_select_fallback_when_valid,
  input logic [31:0] model_req_epoch,
  input logic [31:0] model_req_geometry_handle,
  input logic [31:0] model_req_id,
  input logic model_req_ready,
  input logic [15:0] model_req_stream_velocity_mps,
  input logic [15:0] model_req_timeout_cycles,
  input logic model_req_valid,
  input logic [31:0] model_rsp_drag_force,
  input logic [31:0] model_rsp_epoch,
  input logic [31:0] model_rsp_flow_field_meta,
  input logic [31:0] model_rsp_id,
  input logic [31:0] model_rsp_lift_force,
  input logic model_rsp_status_unavailable,
  input logic model_rsp_status_valid,
  input logic [31:0] model_rsp_surface_pressure,
  input logic model_rsp_valid,
  input logic [15:0] request_timeout_cycles,
  input logic rst_n,
  input logic [15:0] safe_fallback_command_value,
  input logic status_actuator_saturation_fault,
  input logic status_cfg_fault,
  input logic status_faulted,
  input logic status_flow_fault,
  input logic status_geometry_fault,
  input logic [31:0] status_last_accepted_req_id,
  input logic [31:0] status_last_accepted_rsp_id,
  input logic status_mode_fallback,
  input logic status_mode_model,
  input logic status_model_unavailable_fault,
  input logic [31:0] status_req_id,
  input logic status_request_timeout_fault,
  input logic status_response_mismatch_fault,
  input logic [31:0] status_rsp_id,
  input logic status_stale_rejected,
  input logic status_stale_response_fault,
  input logic [15:0] stream_velocity_mps,
  input logic [7:0] telemetry_fault_bits,
  input logic telemetry_last_clamped,
  input logic telemetry_last_fallback,
  input logic [1:0] telemetry_mode,
  input logic telemetry_ready,
  input logic [31:0] telemetry_req_id,
  input logic [31:0] telemetry_rsp_id,
  input logic telemetry_stale,
  input logic telemetry_valid
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(rst_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $error("Reset signal has X/Z state.");
  property p_host_cfg_ready_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_cfg_ready);
  endproperty

  a_host_cfg_ready_known_after_reset: assert property(p_host_cfg_ready_known_after_reset)
    else $error("Signal host_cfg_ready has X/Z after reset release.");
  property p_host_cfg_rdata_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_cfg_rdata);
  endproperty

  a_host_cfg_rdata_known_after_reset: assert property(p_host_cfg_rdata_known_after_reset)
    else $error("Signal host_cfg_rdata has X/Z after reset release.");
  property p_host_cfg_rvalid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(host_cfg_rvalid);
  endproperty

  a_host_cfg_rvalid_known_after_reset: assert property(p_host_cfg_rvalid_known_after_reset)
    else $error("Signal host_cfg_rvalid has X/Z after reset release.");
  property p_model_req_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_valid);
  endproperty

  a_model_req_valid_known_after_reset: assert property(p_model_req_valid_known_after_reset)
    else $error("Signal model_req_valid has X/Z after reset release.");
  property p_model_req_id_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_id);
  endproperty

  a_model_req_id_known_after_reset: assert property(p_model_req_id_known_after_reset)
    else $error("Signal model_req_id has X/Z after reset release.");
  property p_model_req_epoch_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_epoch);
  endproperty

  a_model_req_epoch_known_after_reset: assert property(p_model_req_epoch_known_after_reset)
    else $error("Signal model_req_epoch has X/Z after reset release.");
  property p_model_req_geometry_handle_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_geometry_handle);
  endproperty

  a_model_req_geometry_handle_known_after_reset: assert property(p_model_req_geometry_handle_known_after_reset)
    else $error("Signal model_req_geometry_handle has X/Z after reset release.");
  property p_model_req_stream_velocity_mps_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_stream_velocity_mps);
  endproperty

  a_model_req_stream_velocity_mps_known_after_reset: assert property(p_model_req_stream_velocity_mps_known_after_reset)
    else $error("Signal model_req_stream_velocity_mps has X/Z after reset release.");
  property p_model_req_timeout_cycles_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(model_req_timeout_cycles);
  endproperty

  a_model_req_timeout_cycles_known_after_reset: assert property(p_model_req_timeout_cycles_known_after_reset)
    else $error("Signal model_req_timeout_cycles has X/Z after reset release.");
  property p_actuator_cmd_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(actuator_cmd_valid);
  endproperty

  a_actuator_cmd_valid_known_after_reset: assert property(p_actuator_cmd_valid_known_after_reset)
    else $error("Signal actuator_cmd_valid has X/Z after reset release.");
  property p_actuator_cmd_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(actuator_cmd);
  endproperty

  a_actuator_cmd_known_after_reset: assert property(p_actuator_cmd_known_after_reset)
    else $error("Signal actuator_cmd has X/Z after reset release.");
  property p_actuator_cmd_safe_fallback_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(actuator_cmd_safe_fallback);
  endproperty

  a_actuator_cmd_safe_fallback_known_after_reset: assert property(p_actuator_cmd_safe_fallback_known_after_reset)
    else $error("Signal actuator_cmd_safe_fallback has X/Z after reset release.");

endmodule
