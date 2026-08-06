module AeroGuard_Active_Aerodynamics_Controller(
    clk,
    rst_n,
    i_vehicle_geometry,
    i_flow_conditions,
    i_model_response,
    i_actuator_feedback,
    i_cfg,
    o_model_request,
    o_actuator_command,
    o_safety_state,
    o_telemetry,
    ag_input_validation_geometry_valid,
    ag_input_validation_geometry_error,
    ag_input_validation_flow_valid,
    ag_input_validation_out_of_envelope,
    ag_input_validation_configuration_valid,
    ag_input_validation_geometry_revision,
    ag_input_validation_sanitized_geometry,
    ag_input_validation_sanitized_flow,
    ag_input_validation_reference_operating_tag,
    ag_input_validation_config_fault,
    ag_request_sequencer_geometry_valid,
    ag_request_sequencer_flow_valid,
    ag_request_sequencer_configuration_valid,
    ag_request_sequencer_safety_inhibit,
    ag_request_sequencer_sanitized_geometry,
    ag_request_sequencer_sanitized_flow,
    ag_request_sequencer_geometry_revision,
    ag_request_sequencer_reference_operating_tag,
    ag_request_sequencer_request_id_out,
    ag_request_sequencer_request_timestamp,
    ag_request_sequencer_request_age,
    ag_request_sequencer_request_valid,
    ag_request_sequencer_request_issued,
    ag_response_parser_request_id_expected,
    ag_response_parser_model_valid_in,
    ag_response_parser_response_timeout,
    ag_response_parser_model_data_valid,
    ag_response_parser_response_error,
    ag_response_parser_stale_detected,
    ag_response_parser_response_age,
    ag_response_parser_drag_force,
    ag_response_parser_lift_force,
    ag_response_parser_surface_pressure,
    ag_response_parser_flow_field_meta,
    ag_command_and_safety_fsm_geometry_valid,
    ag_command_and_safety_fsm_flow_valid,
    ag_command_and_safety_fsm_configuration_valid,
    ag_command_and_safety_fsm_geometry_error,
    ag_command_and_safety_fsm_out_of_envelope,
    ag_command_and_safety_fsm_response_error,
    ag_command_and_safety_fsm_stale_detected,
    ag_command_and_safety_fsm_model_data_valid,
    ag_command_and_safety_fsm_drag_force,
    ag_command_and_safety_fsm_lift_force,
    ag_command_and_safety_fsm_surface_pressure,
    ag_command_and_safety_fsm_flow_field_meta,
    ag_command_and_safety_fsm_request_id_in,
    ag_command_and_safety_fsm_actuator_feedback,
    ag_command_and_safety_fsm_cfg,
    ag_command_and_safety_fsm_fallback_active,
    ag_command_and_safety_fsm_clamp_applied,
    ag_command_and_safety_fsm_actuator_fault,
    ag_command_and_safety_fsm_current_state,
    ag_command_and_safety_fsm_last_valid_command,
    ag_command_and_safety_fsm_safety_inhibit
);
input clk;
input rst_n;
input [255:0] i_vehicle_geometry;
input [95:0] i_flow_conditions;
input [191:0] i_model_response;
input [31:0] i_actuator_feedback;
input [255:0] i_cfg;
output [255:0] o_model_request;
output [31:0] o_actuator_command;
output [63:0] o_safety_state;
output [255:0] o_telemetry;
input ag_input_validation_geometry_valid;
input ag_input_validation_geometry_error;
input ag_input_validation_flow_valid;
input ag_input_validation_out_of_envelope;
input ag_input_validation_configuration_valid;
input [15:0] ag_input_validation_geometry_revision;
input [127:0] ag_input_validation_sanitized_geometry;
input [95:0] ag_input_validation_sanitized_flow;
input [15:0] ag_input_validation_reference_operating_tag;
input ag_input_validation_config_fault;
output ag_request_sequencer_geometry_valid;
output ag_request_sequencer_flow_valid;
output ag_request_sequencer_configuration_valid;
output ag_request_sequencer_safety_inhibit;
output [127:0] ag_request_sequencer_sanitized_geometry;
output [95:0] ag_request_sequencer_sanitized_flow;
output [15:0] ag_request_sequencer_geometry_revision;
output [15:0] ag_request_sequencer_reference_operating_tag;
input [15:0] ag_request_sequencer_request_id_out;
input [15:0] ag_request_sequencer_request_timestamp;
input [15:0] ag_request_sequencer_request_age;
input ag_request_sequencer_request_valid;
input ag_request_sequencer_request_issued;
output [15:0] ag_response_parser_request_id_expected;
output ag_response_parser_model_valid_in;
output [15:0] ag_response_parser_response_timeout;
input ag_response_parser_model_data_valid;
input ag_response_parser_response_error;
input ag_response_parser_stale_detected;
input [15:0] ag_response_parser_response_age;
input [31:0] ag_response_parser_drag_force;
input [31:0] ag_response_parser_lift_force;
input [31:0] ag_response_parser_surface_pressure;
input [63:0] ag_response_parser_flow_field_meta;
output ag_command_and_safety_fsm_geometry_valid;
output ag_command_and_safety_fsm_flow_valid;
output ag_command_and_safety_fsm_configuration_valid;
output ag_command_and_safety_fsm_geometry_error;
output ag_command_and_safety_fsm_out_of_envelope;
output ag_command_and_safety_fsm_response_error;
output ag_command_and_safety_fsm_stale_detected;
output ag_command_and_safety_fsm_model_data_valid;
output [31:0] ag_command_and_safety_fsm_drag_force;
output [31:0] ag_command_and_safety_fsm_lift_force;
output [31:0] ag_command_and_safety_fsm_surface_pressure;
output [63:0] ag_command_and_safety_fsm_flow_field_meta;
output [15:0] ag_command_and_safety_fsm_request_id_in;
output [31:0] ag_command_and_safety_fsm_actuator_feedback;
output [255:0] ag_command_and_safety_fsm_cfg;
input ag_command_and_safety_fsm_fallback_active;
input ag_command_and_safety_fsm_clamp_applied;
input ag_command_and_safety_fsm_actuator_fault;
input [7:0] ag_command_and_safety_fsm_current_state;
input [31:0] ag_command_and_safety_fsm_last_valid_command;
input ag_command_and_safety_fsm_safety_inhibit;

wire geometry_valid_w;
wire geometry_error_w;
wire flow_valid_w;
wire out_of_envelope_w;
wire configuration_valid_w;
wire [15:0] geometry_revision_w;
wire [127:0] sanitized_geometry_w;
wire [95:0] sanitized_flow_w;
wire [15:0] reference_operating_tag_w;
wire config_fault_w;

wire request_geom_valid_w;
wire request_flow_valid_w;
wire request_cfg_valid_w;
wire request_safety_inhibit_w;
wire [127:0] request_sanitized_geometry_w;
wire [95:0] request_sanitized_flow_w;
wire [15:0] request_geometry_revision_w;
wire [15:0] request_ref_tag_w;
wire [15:0] request_id_out_w;
wire [15:0] request_timestamp_w;
wire [15:0] request_age_w;
wire request_valid_w;
wire request_issued_w;
wire [255:0] request_model_request_w;
wire [15:0] response_request_id_expected_w;
wire response_model_valid_in_w;
wire [15:0] response_timeout_w;
wire response_model_data_valid_w;
wire response_error_w;
wire stale_detected_w;
wire [15:0] response_age_w;
wire [31:0] drag_force_w;
wire [31:0] lift_force_w;
wire [31:0] surface_pressure_w;
wire [63:0] flow_field_meta_w;
wire fsm_geometry_valid_w;
wire fsm_flow_valid_w;
wire fsm_configuration_valid_w;
wire fsm_geometry_error_w;
wire fsm_out_of_envelope_w;
wire fsm_response_error_w;
wire fsm_stale_detected_w;
wire fsm_model_data_valid_w;
wire [31:0] fsm_drag_force_w;
wire [31:0] fsm_lift_force_w;
wire [31:0] fsm_surface_pressure_w;
wire [63:0] fsm_flow_field_meta_w;
wire [15:0] fsm_request_id_in_w;
wire [31:0] fsm_actuator_feedback_w;
wire [255:0] fsm_cfg_w;
wire fsm_fallback_active_w;
wire fsm_clamp_applied_w;
wire fsm_actuator_fault_w;
wire [7:0] fsm_current_state_w;
wire [31:0] fsm_last_valid_command_w;
wire fsm_safety_inhibit_w;
wire [31:0] actuator_command_w;
wire [63:0] safety_state_w;
wire [255:0] telemetry_w;
ag_input_validation u_ag_input_validation(
    .clk(clk),
    .rst_n(rst_n),
    .i_vehicle_geometry(i_vehicle_geometry),
    .i_flow_conditions(i_flow_conditions),
    .i_cfg(i_cfg),
    .geometry_valid(geometry_valid_w),
    .geometry_error(geometry_error_w),
    .flow_valid(flow_valid_w),
    .out_of_envelope(out_of_envelope_w),
    .configuration_valid(configuration_valid_w),
    .geometry_revision(geometry_revision_w),
    .sanitized_geometry(sanitized_geometry_w),
    .sanitized_flow(sanitized_flow_w),
    .reference_operating_tag(reference_operating_tag_w),
    .config_fault(config_fault_w)
);

assign ag_request_sequencer_geometry_valid = geometry_valid_w;
assign ag_request_sequencer_flow_valid = flow_valid_w;
assign ag_request_sequencer_configuration_valid = configuration_valid_w;
assign ag_request_sequencer_safety_inhibit = request_safety_inhibit_w;
assign ag_request_sequencer_sanitized_geometry = sanitized_geometry_w;
assign ag_request_sequencer_sanitized_flow = sanitized_flow_w;
assign ag_request_sequencer_geometry_revision = geometry_revision_w;
assign ag_request_sequencer_reference_operating_tag = reference_operating_tag_w;

ag_request_sequencer u_ag_request_sequencer(
    .clk(clk),
    .rst_n(rst_n),
    .geometry_valid(ag_request_sequencer_geometry_valid),
    .flow_valid(ag_request_sequencer_flow_valid),
    .configuration_valid(ag_request_sequencer_configuration_valid),
    .safety_inhibit(ag_request_sequencer_safety_inhibit),
    .sanitized_geometry(ag_request_sequencer_sanitized_geometry),
    .sanitized_flow(ag_request_sequencer_sanitized_flow),
    .geometry_revision(ag_request_sequencer_geometry_revision),
    .reference_operating_tag(ag_request_sequencer_reference_operating_tag),
    .request_id_out(request_id_out_w),
    .request_timestamp(request_timestamp_w),
    .request_age(request_age_w),
    .request_valid(request_valid_w),
    .o_model_request(request_model_request_w),
    .request_issued(request_issued_w)
);

assign ag_response_parser_request_id_expected = request_id_out_w;
assign ag_response_parser_model_valid_in = request_valid_w;
assign ag_response_parser_response_timeout = 16'h0010;

ag_response_parser u_ag_response_parser(
    .clk(clk),
    .rst_n(rst_n),
    .i_model_response(i_model_response),
    .request_id_expected(ag_response_parser_request_id_expected),
    .model_valid_in(ag_response_parser_model_valid_in),
    .response_timeout(ag_response_parser_response_timeout),
    .model_data_valid(response_model_data_valid_w),
    .response_error(response_error_w),
    .stale_detected(stale_detected_w),
    .response_age(response_age_w),
    .drag_force(drag_force_w),
    .lift_force(lift_force_w),
    .surface_pressure(surface_pressure_w),
    .flow_field_meta(flow_field_meta_w)
);

assign ag_command_and_safety_fsm_geometry_valid = geometry_valid_w;
assign ag_command_and_safety_fsm_flow_valid = flow_valid_w;
assign ag_command_and_safety_fsm_configuration_valid = configuration_valid_w;
assign ag_command_and_safety_fsm_geometry_error = geometry_error_w;
assign ag_command_and_safety_fsm_out_of_envelope = out_of_envelope_w;
assign ag_command_and_safety_fsm_response_error = response_error_w;
assign ag_command_and_safety_fsm_stale_detected = stale_detected_w;
assign ag_command_and_safety_fsm_model_data_valid = response_model_data_valid_w;
assign ag_command_and_safety_fsm_drag_force = drag_force_w;
assign ag_command_and_safety_fsm_lift_force = lift_force_w;
assign ag_command_and_safety_fsm_surface_pressure = surface_pressure_w;
assign ag_command_and_safety_fsm_flow_field_meta = flow_field_meta_w;
assign ag_command_and_safety_fsm_request_id_in = request_id_out_w;
assign ag_command_and_safety_fsm_actuator_feedback = i_actuator_feedback;
assign ag_command_and_safety_fsm_cfg = i_cfg;

ag_command_and_safety_fsm u_ag_command_and_safety_fsm(
    .clk(clk),
    .rst_n(rst_n),
    .geometry_valid(ag_command_and_safety_fsm_geometry_valid),
    .flow_valid(ag_command_and_safety_fsm_flow_valid),
    .configuration_valid(ag_command_and_safety_fsm_configuration_valid),
    .geometry_error(ag_command_and_safety_fsm_geometry_error),
    .out_of_envelope(ag_command_and_safety_fsm_out_of_envelope),
    .response_error(ag_command_and_safety_fsm_response_error),
    .stale_detected(ag_command_and_safety_fsm_stale_detected),
    .model_data_valid(ag_command_and_safety_fsm_model_data_valid),
    .drag_force(ag_command_and_safety_fsm_drag_force),
    .lift_force(ag_command_and_safety_fsm_lift_force),
    .surface_pressure(ag_command_and_safety_fsm_surface_pressure),
    .flow_field_meta(ag_command_and_safety_fsm_flow_field_meta),
    .request_id_in(ag_command_and_safety_fsm_request_id_in),
    .actuator_feedback(ag_command_and_safety_fsm_actuator_feedback),
    .cfg(ag_command_and_safety_fsm_cfg),
    .o_actuator_command(actuator_command_w),
    .o_safety_state(safety_state_w),
    .o_telemetry(telemetry_w),
    .fallback_active(fsm_fallback_active_w),
    .clamp_applied(fsm_clamp_applied_w),
    .actuator_fault(fsm_actuator_fault_w),
    .current_state(fsm_current_state_w),
    .last_valid_command(fsm_last_valid_command_w),
    .safety_inhibit(fsm_safety_inhibit_w)
);

assign o_model_request = request_model_request_w;
assign o_actuator_command = actuator_command_w;
assign o_safety_state = safety_state_w;
assign o_telemetry = telemetry_w;

endmodule
