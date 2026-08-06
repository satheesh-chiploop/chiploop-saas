module active_aero_supervisor (
    input         clk,
    input         rst_n,
    input         control_valid,
    input         vehicle_geometry_valid,
    input         flow_conditions_valid,
    input  [31:0] stream_velocity_mps,
    input  [127:0] geometry_ref,
    input         host_fallback_route_en,
    input  [31:0] host_operating_en_min_mps,
    input  [31:0] host_operating_en_max_mps,
    input  [31:0] host_freshness_window_cycles,
    input  [31:0] host_response_timeout_cycles,
    input  [31:0] host_fallback_command,
    input         host_clear_sticky,
    input         model_response_valid,
    input  [255:0] model_response_payload,
    output        model_request_valid,
    output [255:0] model_request_payload,
    output        actuator_cmd_valid,
    output [31:0] actuator_cmd,
    output [7:0] safety_status,
    output [31:0] telemetry_accepted_response_count,
    output [31:0] telemetry_rejected_stale_count,
    output [31:0] telemetry_clamp_event_count,
    output [31:0] telemetry_timeout_event_count,
    output [31:0] telemetry_fallback_activation_count,
    output [7:0] telemetry_sticky_status
);
    wire [15:0] request_id;
    wire [15:0] request_seq;
    wire [31:0] request_timestamp;
    wire        request_pending;
    wire        request_launch_grant;
    wire        response_accepted;
    wire        response_stale;
    wire        response_invalid;
    wire        response_timeout;
    wire [31:0] drag_force;
    wire [31:0] lift_force;
    wire [31:0] surface_pressure;
    wire [63:0] flow_field_meta;
    wire [31:0] command_raw;
    wire        command_raw_valid;
    wire        fallback_active;
    wire        clamp_active;
    wire [31:0] bounded_command;
    wire        bounded_command_valid;
    wire        stale_reject;
    wire        timeout_fault;
    wire        invalid_response_fault;
    wire [7:0] sticky_status;
    wire        envelope_violation;

wire command_raw_valid_unused_from_u_response_validator_response_payload_valid_out;
wire [31:0] host_fallback_command_from_u_command_synthesizer;
    assign request_launch_grant = 1'b1;

    request_manager u_request_manager (
        .clk(clk),
        .rst_n(rst_n),
        .control_valid(control_valid),
        .vehicle_geometry_valid(vehicle_geometry_valid),
        .flow_conditions_valid(flow_conditions_valid),
        .stream_velocity_mps(stream_velocity_mps),
        .geometry_ref(geometry_ref),
        .host_fallback_route_en(host_fallback_route_en),
        .host_operating_en_min_mps(host_operating_en_min_mps),
        .host_operating_en_max_mps(host_operating_en_max_mps),
        .request_launch_grant(request_launch_grant),
        .outstanding_clear(bounded_command_valid | invalid_response_fault),
        .request_id_out(request_id),
        .request_seq_out(request_seq),
        .request_timestamp_out(request_timestamp),
        .request_payload_out(model_request_payload),
        .request_valid_out(model_request_valid),
        .request_pending_out(request_pending),
        .envelope_violation_out(envelope_violation)
    );

    response_validator u_response_validator (
        .clk(clk),
        .rst_n(rst_n),
        .model_response_valid(model_response_valid),
        .model_response_payload(model_response_payload),
        .outstanding_request_id(request_id),
        .outstanding_request_seq(request_seq),
        .outstanding_timestamp(request_timestamp),
        .freshness_window_cycles(host_freshness_window_cycles),
        .response_accepted_out(response_accepted),
        .response_stale_out(response_stale),
        .response_invalid_out(response_invalid),
        .response_timeout_out(response_timeout),
        .drag_force_out(drag_force),
        .lift_force_out(lift_force),
        .surface_pressure_out(surface_pressure),
        .flow_field_meta_out(flow_field_meta),
        .response_payload_valid_out(command_raw_valid_unused_from_u_response_validator_response_payload_valid_out)
    );

    command_synthesizer u_command_synthesizer (
        .clk(clk),
        .rst_n(rst_n),
        .response_payload_valid_in(response_accepted),
        .drag_force_in(drag_force),
        .lift_force_in(lift_force),
        .surface_pressure_in(surface_pressure),
        .flow_field_meta_in(flow_field_meta),
        .fallback_active_in(fallback_active),
        .safe_fallback_command_in(host_fallback_command_from_u_command_synthesizer),
        .command_raw_out(command_raw),
        .command_valid_out(command_raw_valid),
        .command_source_fallback_out()
    );

    clamp_unit u_clamp_unit (
        .clk(clk),
        .rst_n(rst_n),
        .command_in(command_raw),
        .command_valid_in(command_raw_valid),
        .command_min_in(host_operating_en_min_mps),
        .command_max_in(host_operating_en_max_mps),
        .command_out(bounded_command),
        .command_valid_out(bounded_command_valid),
        .clamp_active_out(clamp_active)
    );

    safety_supervisor u_safety_supervisor (
        .clk(clk),
        .rst_n(rst_n),
        .envelope_violation_in(envelope_violation),
        .response_stale_in(response_stale),
        .response_invalid_in(response_invalid),
        .response_timeout_in(response_timeout),
        .clamp_active_in(clamp_active),
        .command_out_of_bounds_in(1'b0),
        .internal_fault_in(request_pending),
        .host_clear_sticky(host_clear_sticky),
        .stale_reject_out(stale_reject),
        .timeout_fault_out(timeout_fault),
        .invalid_response_out(invalid_response_fault),
        .clamp_active_out(),
        .fallback_active_out(fallback_active),
        .safety_status_out(safety_status),
        .sticky_status_out(sticky_status)
    );

    telemetry_monitor u_telemetry_monitor (
        .clk(clk),
        .rst_n(rst_n),
        .accepted_response_pulse(response_accepted),
        .rejected_stale_pulse(stale_reject),
        .clamp_event_pulse(clamp_active),
        .timeout_event_pulse(timeout_fault),
        .fallback_activation_pulse(fallback_active),
        .sticky_clear_in(host_clear_sticky),
        .accepted_response_count_out(telemetry_accepted_response_count),
        .rejected_stale_count_out(telemetry_rejected_stale_count),
        .clamp_event_count_out(telemetry_clamp_event_count),
        .timeout_event_count_out(telemetry_timeout_event_count),
        .fallback_activation_count_out(telemetry_fallback_activation_count),
        .sticky_status_out(sticky_status)
    );

    assign actuator_cmd_valid = bounded_command_valid;
    assign actuator_cmd = bounded_command;
    assign telemetry_sticky_status = sticky_status;

endmodule
