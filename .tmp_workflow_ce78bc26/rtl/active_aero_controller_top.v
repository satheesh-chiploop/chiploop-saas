module active_aero_controller_top (
    clk,
    reset_n,
    vehicle_geometry_valid,
    geometry_format,
    geometry_source,
    geometry_metadata,
    stream_velocity_mps,
    flow_metadata,
    req_ready,
    resp_valid,
    resp_id,
    resp_timestamp,
    resp_payload,
    fault_in,
    req_valid,
    req_id,
    req_payload,
    actuator_command,
    actuator_command_valid,
    status_telemetry,
    fault_code
);
input clk;
input reset_n;
input vehicle_geometry_valid;
input [2:0] geometry_format;
input [3:0] geometry_source;
input [63:0] geometry_metadata;
input [15:0] stream_velocity_mps;
input [31:0] flow_metadata;
input req_ready;
input resp_valid;
input [15:0] resp_id;
input [31:0] resp_timestamp;
input [255:0] resp_payload;
input fault_in;
output req_valid;
output [15:0] req_id;
output [319:0] req_payload;
output [63:0] actuator_command;
output actuator_command_valid;
output [15:0] status_telemetry;
output [3:0] fault_code;
wire geometry_valid;
wire geometry_reject;
wire [127:0] geometry_descriptor;
wire flow_valid;
wire envelope_fault;
wire nominal_condition;
wire [63:0] flow_descriptor;
wire request_outstanding;
wire [15:0] outstanding_req_id;
wire [31:0] outstanding_req_timestamp;
wire fresh_response_pulse;
wire response_mismatch;
wire response_fresh;
wire [255:0] validated_resp_payload;
wire model_output_valid;
wire [31:0] drag_force;
wire [31:0] lift_force;
wire [31:0] surface_pressure;
wire [127:0] flow_field_metadata;
wire command_enable;
wire [63:0] command_vector;
wire supervisor_release;
wire fallback_active;
wire stale_command;
wire [63:0] saturated_command;
wire saturated_valid;
wire command_clamped;
wire [63:0] fallback_output;
wire fallback_valid;

geometry_ingress u_geometry_ingress (
    .clk(clk),
    .reset_n(reset_n),
    .vehicle_geometry_valid(vehicle_geometry_valid),
    .geometry_format(geometry_format),
    .geometry_source(geometry_source),
    .geometry_metadata(geometry_metadata),
    .geometry_valid(geometry_valid),
    .geometry_reject(geometry_reject),
    .geometry_descriptor(geometry_descriptor)
);

flow_condition_checker u_flow_condition_checker (
    .clk(clk),
    .reset_n(reset_n),
    .stream_velocity_mps(stream_velocity_mps),
    .flow_metadata(flow_metadata),
    .flow_valid(flow_valid),
    .envelope_fault(envelope_fault),
    .nominal_condition(nominal_condition),
    .flow_descriptor(flow_descriptor)
);

model_txn_mgr u_model_txn_mgr (
    .clk(clk),
    .reset_n(reset_n),
    .geometry_valid(geometry_valid),
    .geometry_descriptor(geometry_descriptor),
    .flow_valid(flow_valid),
    .flow_descriptor(flow_descriptor),
    .safe_mode(safe_mode),
    .fallback_active(fallback_active),
    .req_ready(req_ready),
    .resp_valid(resp_valid),
    .resp_id(resp_id),
    .resp_timestamp(resp_timestamp),
    .resp_payload(resp_payload),
    .req_valid(req_valid),
    .req_id(req_id),
    .req_payload(req_payload),
    .request_outstanding(request_outstanding),
    .outstanding_req_id(outstanding_req_id),
    .outstanding_req_timestamp(outstanding_req_timestamp),
    .fresh_response_pulse(fresh_response_pulse),
    .response_mismatch(response_mismatch),
    .response_fresh(response_fresh),
    .validated_resp_payload(validated_resp_payload)
);

response_validator u_response_validator (
    .clk(clk),
    .reset_n(reset_n),
    .resp_valid(resp_valid),
    .resp_id(resp_id),
    .resp_timestamp(resp_timestamp),
    .resp_payload(validated_resp_payload),
    .outstanding_req_id(outstanding_req_id),
    .outstanding_req_timestamp(outstanding_req_timestamp),
    .fresh_response_pulse(fresh_response_pulse),
    .response_mismatch(response_mismatch),
    .model_output_valid(model_output_valid),
    .drag_force(drag_force),
    .lift_force(lift_force),
    .surface_pressure(surface_pressure),
    .flow_field_metadata(flow_field_metadata),
    .stale_response(stale_response)
);

aero_control_policy u_aero_control_policy (
    .clk(clk),
    .reset_n(reset_n),
    .model_output_valid(model_output_valid),
    .drag_force(drag_force),
    .lift_force(lift_force),
    .surface_pressure(surface_pressure),
    .flow_field_metadata(flow_field_metadata),
    .command_enable(command_enable),
    .command_vector(command_vector)
);

command_saturator u_command_saturator (
    .clk(clk),
    .reset_n(reset_n),
    .command_enable(command_enable),
    .command_vector(command_vector),
    .supervisor_release(supervisor_release),
    .min_bound(64'h0000000000000000),
    .max_bound(64'hFFFFFFFFFFFFFFFF),
    .rate_limit_step(64'h0000000000000001),
    .saturated_command(saturated_command),
    .saturated_valid(saturated_valid),
    .command_clamped(command_clamped)
);

safety_supervisor u_safety_supervisor (
    .clk(clk),
    .reset_n(reset_n),
    .geometry_reject(geometry_reject),
    .envelope_fault(envelope_fault),
    .response_mismatch(response_mismatch),
    .response_fresh(response_fresh),
    .stale_response(stale_response),
    .model_output_valid(model_output_valid),
    .command_clamped(command_clamped),
    .fault_in(fault_in),
    .request_outstanding(request_outstanding),
    .safe_mode(safe_mode),
    .supervisor_release(supervisor_release),
    .fallback_active(fallback_active),
    .stale_command(stale_command),
    .fault_code(fault_code)
);

fallback_fsm u_fallback_fsm (
    .clk(clk),
    .reset_n(reset_n),
    .safe_mode(safe_mode),
    .fallback_setpoint_a(16'h0001),
    .fallback_setpoint_b(16'h0002),
    .fallback_setpoint_c(16'h0003),
    .fallback_setpoint_d(16'h0004),
    .fallback_output(fallback_output),
    .fallback_valid(fallback_valid),
    .fallback_active()
);

assign actuator_command = safe_mode ? fallback_output : saturated_command;
assign actuator_command_valid = safe_mode ? fallback_valid : saturated_valid;
assign status_telemetry[0] = geometry_valid;
assign status_telemetry[1] = flow_valid;
assign status_telemetry[2] = request_outstanding;
assign status_telemetry[3] = response_fresh;
assign status_telemetry[4] = safe_mode;
assign status_telemetry[5] = envelope_fault;
assign status_telemetry[6] = stale_response;
assign status_telemetry[7] = command_clamped;
assign status_telemetry[8] = fallback_active;
assign status_telemetry[9] = model_output_valid;
assign status_telemetry[10] = geometry_reject;
assign status_telemetry[11] = response_mismatch;
assign status_telemetry[12] = nominal_condition;
assign status_telemetry[13] = fallback_valid;
assign status_telemetry[14] = command_enable;
assign status_telemetry[15] = supervisor_release;

endmodule
