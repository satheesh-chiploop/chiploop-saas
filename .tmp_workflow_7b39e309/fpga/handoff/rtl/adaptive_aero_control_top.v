module adaptive_aero_control_top(
    clk,
    reset_n,
    spi_cs_n,
    spi_sclk,
    spi_mosi,
    spi_miso,
    host_cmd_valid,
    host_cmd_opcode,
    host_cmd_data,
    host_rsp_ready,
    host_rsp_valid,
    host_rsp_data,
    host_fault_valid,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    actuator_cmd_valid,
    actuator_cmd_data,
    actuator_cmd_saturated,
    actuator_cmd_latched_fault,
    sensor_airdata_valid,
    sensor_airspeed,
    sensor_altitude,
    sensor_angle_of_attack,
    sensor_gload,
    status_valid,
    status_code,
    fault_latched,
    history_csb_n,
    history_we_n,
    history_addr,
    history_din,
    history_dout,
    payload_csb_n,
    payload_we_n,
    payload_addr,
    payload_din,
    payload_dout
);
input clk;
input reset_n;
input spi_cs_n;
input spi_sclk;
input spi_mosi;
output spi_miso;
input host_cmd_valid;
input [7:0] host_cmd_opcode;
input [31:0] host_cmd_data;
input host_rsp_ready;
output host_rsp_valid;
output [31:0] host_rsp_data;
output host_fault_valid;
output model_req_valid;
output [31:0] model_req_data;
input model_req_ready;
input model_rsp_valid;
input [31:0] model_rsp_data;
output model_rsp_ready;
output actuator_cmd_valid;
output [15:0] actuator_cmd_data;
output actuator_cmd_saturated;
output actuator_cmd_latched_fault;
input sensor_airdata_valid;
input [15:0] sensor_airspeed;
input [15:0] sensor_altitude;
input [15:0] sensor_angle_of_attack;
input [15:0] sensor_gload;
output status_valid;
output [7:0] status_code;
output fault_latched;
output history_csb_n;
output history_we_n;
output [7:0] history_addr;
output [31:0] history_din;
input [31:0] history_dout;
output payload_csb_n;
output payload_we_n;
output [6:0] payload_addr;
output [31:0] payload_din;
input [31:0] payload_dout;
wire model_req_valid_t;
wire [31:0] model_req_data_t;
wire host_rsp_valid_t;
wire [31:0] host_rsp_data_t;
wire model_rsp_ready_t;
wire fault_latched_v;
wire status_valid_v;
wire [7:0] status_code_v;
wire validated_req_valid;
wire [31:0] validated_req_data;
wire validated_rsp_valid;
wire [31:0] validated_rsp_data;
wire command_allowed;
wire model_trace_valid;
wire [31:0] model_trace_data;
wire history_commit_valid;
wire [7:0] history_commit_tag;
wire actuator_cmd_valid_l;
wire [15:0] actuator_cmd_data_l;
wire actuator_cmd_saturated_l;
wire actuator_cmd_latched_fault_l;
wire fault_latched_a;

wire fault_latched_top;
wire [31:0] control_validation_core_validated_req_data;
wire control_validation_core_validated_req_valid;
assign model_req_valid = model_req_valid_t;
assign model_req_data = model_req_data_t;
assign host_rsp_valid = host_rsp_valid_t;
assign host_rsp_data = host_rsp_data_t;
assign model_rsp_ready = model_rsp_ready_t;
assign status_valid = status_valid_v;
assign status_code = history_commit_valid ? history_commit_tag : status_code_v;
assign fault_latched = fault_latched_a;
assign host_fault_valid = fault_latched_a | history_commit_valid;
assign actuator_cmd_valid = actuator_cmd_valid_l;
assign actuator_cmd_data = actuator_cmd_data_l;
assign actuator_cmd_saturated = actuator_cmd_saturated_l;
assign actuator_cmd_latched_fault = actuator_cmd_latched_fault_l;

aero_transport_fsm u_aero_transport_fsm(
    .clk(clk),
    .reset_n(reset_n),
    .spi_cs_n(spi_cs_n),
    .spi_sclk(spi_sclk),
    .spi_mosi(spi_mosi),
    .spi_miso(spi_miso),
    .host_cmd_valid(host_cmd_valid),
    .host_cmd_opcode(host_cmd_opcode),
    .host_cmd_data(host_cmd_data),
    .host_rsp_ready(host_rsp_ready),
    .host_rsp_valid(host_rsp_valid_t),
    .host_rsp_data(host_rsp_data_t),
    .model_req_valid(model_req_valid_t),
    .model_req_data(model_req_data_t),
    .model_req_ready(model_req_ready),
    .fault_latched(fault_latched_a),
    .status_valid(status_valid_v),
    .status_code(status_code_v)
);

control_validation_core u_control_validation_core(
    .clk(clk),
    .reset_n(reset_n),
    .host_cmd_valid(host_cmd_valid),
    .host_cmd_opcode(host_cmd_opcode),
    .host_cmd_data(host_cmd_data),
    .sensor_airdata_valid(sensor_airdata_valid),
    .sensor_airspeed(sensor_airspeed),
    .sensor_altitude(sensor_altitude),
    .sensor_angle_of_attack(sensor_angle_of_attack),
    .sensor_gload(sensor_gload),
    .model_req_valid(model_req_valid_t),
    .model_req_data(model_req_data_t),
    .model_req_ready(model_req_ready),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(model_rsp_ready_t),
    .fault_latched(fault_latched_v),
    .status_valid(status_valid_v),
    .status_code(status_code_v),
    .validated_req_valid(validated_req_valid),
    .validated_req_data(validated_req_data),
    .validated_rsp_valid(validated_rsp_valid),
    .validated_rsp_data(validated_rsp_data),
    .command_allowed(command_allowed)
);

domino_surrogate_interface u_domino_surrogate_interface(
    .clk(clk),
    .reset_n(reset_n),
    .validated_req_valid(validated_req_valid),
    .validated_req_data(validated_req_data),
    .validated_rsp_valid(validated_rsp_valid),
    .validated_rsp_data(validated_rsp_data),
    .model_req_valid(),
    .model_req_data(),
    .model_req_ready(model_req_ready),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(),
    .payload_csb_n(payload_csb_n),
    .payload_we_n(payload_we_n),
    .payload_addr(payload_addr),
    .payload_din(payload_din),
    .payload_dout(payload_dout),
    .model_trace_valid(model_trace_valid),
    .model_trace_data(model_trace_data)
);

actuator_command_limiter u_actuator_command_limiter(
    .clk(clk),
    .reset_n(reset_n),
    .command_allowed(command_allowed),
    .validated_rsp_valid(validated_rsp_valid),
    .validated_rsp_data(validated_rsp_data),
    .validated_req_valid(validated_req_valid),
    .validated_req_data(validated_req_data),
    .actuator_cmd_valid(actuator_cmd_valid_l),
    .actuator_cmd_data(actuator_cmd_data_l),
    .actuator_cmd_saturated(actuator_cmd_saturated_l),
    .actuator_cmd_latched_fault(actuator_cmd_latched_fault_l),
    .fault_latched(fault_latched_a)
);

aero_history_logger u_aero_history_logger(
    .clk(clk),
    .reset_n(reset_n),
    .status_valid(status_valid_v),
    .status_code(status_code_v),
    .fault_latched(fault_latched_a),
    .host_cmd_valid(host_cmd_valid),
    .host_cmd_opcode(host_cmd_opcode),
    .host_cmd_data(host_cmd_data),
    .sensor_airdata_valid(sensor_airdata_valid),
    .sensor_airspeed(sensor_airspeed),
    .sensor_altitude(sensor_altitude),
    .sensor_angle_of_attack(sensor_angle_of_attack),
    .sensor_gload(sensor_gload),
    .history_csb_n(history_csb_n),
    .history_we_n(history_we_n),
    .history_addr(history_addr),
    .history_din(history_din),
    .history_dout(history_dout),
    .history_commit_valid(history_commit_valid),
    .history_commit_tag(history_commit_tag)
);

endmodule
