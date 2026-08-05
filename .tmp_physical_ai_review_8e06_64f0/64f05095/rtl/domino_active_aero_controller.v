module domino_active_aero_controller (
    clk,
    rst_n,
    vehicle_geometry_valid,
    vehicle_geometry_ready,
    vehicle_geometry,
    flow_conditions_valid,
    flow_conditions_ready,
    flow_conditions,
    model_req_valid,
    model_req_ready,
    model_req_id,
    model_req_timestamp,
    model_req_geometry,
    model_req_stream_velocity_mps,
    model_req_geometry_tag,
    model_resp_ready,
    model_resp_valid,
    model_resp_id,
    model_resp_timestamp,
    model_resp_drag_force,
    model_resp_lift_force,
    model_resp_surface_pressure,
    model_resp_flow_field_meta,
    actuator_cmd_valid,
    actuator_cmd_ready,
    actuator_cmd,
    fault_valid,
    fault_code,
    request_id_telemetry,
    response_match,
    freshness_ok,
    clamp_event,
    fallback_active,
    source_select,
    cfg_load_done,
    cfg_clear_faults,
    cfg_watchdog_threshold,
    cfg_freshness_threshold,
    cfg_reference_stream_velocity_mps,
    cfg_geometry_provenance_tag,
    cfg_safe_actuator_cmd,
    cfg_actuator_min,
    cfg_actuator_max,
    cfg_cmd_gain_drag,
    cfg_cmd_gain_lift,
    cfg_cmd_bias,
    cfg_fault_clear_sticky
);

input clk;
input rst_n;
input vehicle_geometry_valid;
output vehicle_geometry_ready;
input [63:0] vehicle_geometry;
input flow_conditions_valid;
output flow_conditions_ready;
input [31:0] flow_conditions;
output model_req_valid;
input model_req_ready;
output [15:0] model_req_id;
output [15:0] model_req_timestamp;
output [63:0] model_req_geometry;
output [15:0] model_req_stream_velocity_mps;
output [7:0] model_req_geometry_tag;
output model_resp_ready;
input model_resp_valid;
input [15:0] model_resp_id;
input [15:0] model_resp_timestamp;
input [23:0] model_resp_drag_force;
input [23:0] model_resp_lift_force;
input [15:0] model_resp_surface_pressure;
input [15:0] model_resp_flow_field_meta;
output actuator_cmd_valid;
input actuator_cmd_ready;
output [31:0] actuator_cmd;
output fault_valid;
output [15:0] fault_code;
output [15:0] request_id_telemetry;
output response_match;
output freshness_ok;
output clamp_event;
output fallback_active;
output source_select;
input cfg_load_done;
input cfg_clear_faults;
input [15:0] cfg_watchdog_threshold;
input [15:0] cfg_freshness_threshold;
input [15:0] cfg_reference_stream_velocity_mps;
input [7:0] cfg_geometry_provenance_tag;
input [31:0] cfg_safe_actuator_cmd;
input [31:0] cfg_actuator_min;
input [31:0] cfg_actuator_max;
input [15:0] cfg_cmd_gain_drag;
input [15:0] cfg_cmd_gain_lift;
input [31:0] cfg_cmd_bias;
input cfg_fault_clear_sticky;

wire [15:0] req_request_id;
wire [15:0] req_timestamp;
wire [63:0] req_payload_geometry;
wire [15:0] req_payload_velocity;
wire [7:0] req_payload_geometry_tag;
wire request_valid_to_runtime;
wire request_ready_from_runtime;
wire response_match_internal;
wire freshness_ok_internal;
wire qualified_response_valid;
wire [23:0] qualified_response_drag_force;
wire [23:0] qualified_response_lift_force;
wire [15:0] qualified_response_surface_pressure;
wire [15:0] qualified_response_flow_field_meta;
wire raw_cmd_valid_internal;
wire [31:0] raw_actuator_cmd_internal;
wire clamped_cmd_valid_internal;
wire [31:0] clamped_actuator_cmd_internal;
wire clamp_event_internal;
wire fallback_cmd_valid_internal;
wire [31:0] fallback_cmd_internal;
wire fallback_active_internal;
wire timeout_event_internal;
wire stale_or_mismatch_fault_internal;
wire model_unavailable_fault_internal;
wire invalid_input_fault_internal;

wire cfg_load_done_from_u_request_orchestrator;
assign request_id_telemetry = req_request_id;
assign model_req_id = req_request_id;
assign model_req_timestamp = req_timestamp;
assign model_req_geometry = req_payload_geometry;
assign model_req_stream_velocity_mps = req_payload_velocity;
assign model_req_geometry_tag = req_payload_geometry_tag;
assign model_req_valid = request_valid_to_runtime;
assign response_match = response_match_internal;
assign freshness_ok = freshness_ok_internal;
assign clamp_event = clamp_event_internal;
assign fallback_active = fallback_active_internal;
assign model_resp_ready = 1'b1;
assign actuator_cmd_valid = clamped_cmd_valid_internal | fallback_cmd_valid_internal;
assign actuator_cmd = clamped_cmd_valid_internal ? clamped_actuator_cmd_internal : fallback_cmd_internal;
assign fault_valid = 1'b1;
assign fault_code = {11'b0, timeout_event_internal | stale_or_mismatch_fault_internal | invalid_input_fault_internal | model_unavailable_fault_internal, 4'b0000};
assign source_select = clamped_cmd_valid_internal & ~fallback_active_internal;
assign model_unavailable_fault_internal = ~cfg_load_done;
assign invalid_input_fault_internal = clamp_event_internal;

request_orchestrator u_request_orchestrator (
    .clk(clk),
    .rst_n(rst_n),
    .vehicle_geometry_valid(vehicle_geometry_valid),
    .vehicle_geometry_ready(vehicle_geometry_ready),
    .vehicle_geometry(vehicle_geometry),
    .flow_conditions_valid(flow_conditions_valid),
    .flow_conditions_ready(flow_conditions_ready),
    .flow_conditions(flow_conditions),
    .cfg_load_done(cfg_load_done_from_u_request_orchestrator),
    .cfg_watchdog_threshold(cfg_watchdog_threshold),
    .cfg_reference_stream_velocity_mps(cfg_reference_stream_velocity_mps),
    .cfg_geometry_provenance_tag(cfg_geometry_provenance_tag),
    .request_id_out(req_request_id),
    .timestamp_out(req_timestamp),
    .model_req_valid(request_valid_to_runtime),
    .model_req_ready(request_ready_from_runtime),
    .model_req_id(),
    .model_req_timestamp(),
    .model_req_geometry(req_payload_geometry),
    .model_req_stream_velocity_mps(req_payload_velocity),
    .model_req_geometry_tag(req_payload_geometry_tag),
    .outstanding_valid(),
    .timeout_event(timeout_event_internal)
);

domino_runtime_interface u_domino_runtime_interface (
    .clk(clk),
    .rst_n(rst_n),
    .model_req_valid(request_valid_to_runtime),
    .model_req_ready(request_ready_from_runtime),
    .model_req_id(req_request_id),
    .model_req_timestamp(req_timestamp),
    .model_req_geometry(req_payload_geometry),
    .model_req_stream_velocity_mps(req_payload_velocity),
    .model_req_geometry_tag(req_payload_geometry_tag),
    .model_resp_ready(model_resp_ready),
    .model_resp_valid(model_resp_valid),
    .model_resp_id(model_resp_id),
    .model_resp_timestamp(model_resp_timestamp),
    .model_resp_drag_force(model_resp_drag_force),
    .model_resp_lift_force(model_resp_lift_force),
    .model_resp_surface_pressure(model_resp_surface_pressure),
    .model_resp_flow_field_meta(model_resp_flow_field_meta),
    .response_match(response_match_internal),
    .freshness_ok(freshness_ok_internal),
    .response_valid_qualified(qualified_response_valid),
    .response_drag_force(qualified_response_drag_force),
    .response_lift_force(qualified_response_lift_force),
    .response_surface_pressure(qualified_response_surface_pressure),
    .response_flow_field_meta(qualified_response_flow_field_meta),
    .stale_or_mismatch_fault(stale_or_mismatch_fault_internal)
);

command_synthesis_engine u_command_synthesis_engine (
    .clk(clk),
    .rst_n(rst_n),
    .response_valid_qualified(qualified_response_valid),
    .response_drag_force(qualified_response_drag_force),
    .response_lift_force(qualified_response_lift_force),
    .response_surface_pressure(qualified_response_surface_pressure),
    .response_flow_field_meta(qualified_response_flow_field_meta),
    .cfg_cmd_gain_drag(cfg_cmd_gain_drag),
    .cfg_cmd_gain_lift(cfg_cmd_gain_lift),
    .cfg_cmd_bias(cfg_cmd_bias),
    .raw_actuator_cmd(raw_actuator_cmd_internal),
    .raw_cmd_valid(raw_cmd_valid_internal)
);

actuator_clamper u_actuator_clamper (
    .clk(clk),
    .rst_n(rst_n),
    .raw_cmd_valid(raw_cmd_valid_internal),
    .raw_actuator_cmd(raw_actuator_cmd_internal),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .clamped_cmd_valid(clamped_cmd_valid_internal),
    .clamped_actuator_cmd(clamped_actuator_cmd_internal),
    .clamp_event(clamp_event_internal)
);

safe_fallback_manager u_safe_fallback_manager (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_load_done(cfg_load_done),
    .fault_in(stale_or_mismatch_fault_internal | timeout_event_internal | invalid_input_fault_internal | model_unavailable_fault_internal),
    .timeout_event(timeout_event_internal),
    .stale_or_mismatch_fault(stale_or_mismatch_fault_internal),
    .payload_corruption_fault(1'b0),
    .model_unavailable_fault(model_unavailable_fault_internal),
    .invalid_input_fault(invalid_input_fault_internal),
    .cfg_safe_actuator_cmd(cfg_safe_actuator_cmd),
    .fallback_cmd(fallback_cmd_internal),
    .fallback_cmd_valid(fallback_cmd_valid_internal),
    .fallback_active(fallback_active_internal)
);

safety_supervisor u_safety_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .clamped_cmd_valid(clamped_cmd_valid_internal),
    .clamped_actuator_cmd(clamped_actuator_cmd_internal),
    .fallback_cmd_valid(fallback_cmd_valid_internal),
    .fallback_cmd(fallback_cmd_internal),
    .fallback_active(fallback_active_internal),
    .response_match(response_match_internal),
    .freshness_ok(freshness_ok_internal),
    .timeout_event(timeout_event_internal),
    .stale_or_mismatch_fault(stale_or_mismatch_fault_internal),
    .invalid_input_fault(invalid_input_fault_internal),
    .payload_corruption_fault(1'b0),
    .model_unavailable_fault(model_unavailable_fault_internal),
    .cfg_load_done(cfg_load_done),
    .cfg_clear_faults(cfg_clear_faults),
    .cfg_fault_clear_sticky(cfg_fault_clear_sticky),
    .actuator_cmd_valid(),
    .actuator_cmd(),
    .fault_valid(),
    .fault_code(),
    .source_select(),
    .sticky_fault_latched()
);

endmodule
