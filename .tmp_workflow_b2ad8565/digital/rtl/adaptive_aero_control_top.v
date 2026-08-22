module adaptive_aero_control_top (
    input         clk,
    input         rst_n,
    input         mmio_valid,
    input         mmio_write,
    input  [7:0] mmio_addr,
    input  [63:0] mmio_wdata,
    output [63:0] mmio_rdata,
    output        mmio_ready,
    input         cmd_ready,
    output        cmd_valid,
    output [79:0] cmd_data,
    input         rsp_valid,
    input  [79:0] rsp_data,
    output        rsp_ready,
    output [31:0] actuator_cmd,
    output        actuator_cmd_valid,
    output        safe_fallback,
    output        fault_irq
);
wire cfg_enable;
wire [2:0] cfg_mode;
wire [15:0] cfg_timeout_threshold;
wire [15:0] cfg_request_seq_seed;
wire [15:0] cfg_response_age_limit;
wire [31:0] cfg_actuator_min;
wire [31:0] cfg_actuator_max;
wire cfg_slew_enable;
wire [15:0] cfg_slew_limit;
wire [2:0]  cfg_safe_selector;
wire cfg_fault_clear_w1c;
wire        fault_status;
wire [7:0]  fault_cause;
wire [15:0] revision_id;
wire [31:0] last_good_cmd;
wire [15:0] timeout_counter_snapshot;
wire [15:0] request_id_snapshot;
wire        status_snapshot_valid;
wire request_busy;
wire [15:0] request_id;
wire validated_response_valid;
wire [31:0] validated_response_data;
wire response_reject;
wire [3:0]  response_reject_code;
wire [15:0] response_age_snapshot;
wire fault_latched;
wire cfg_fault_clear_w1c_unused_from_u_control_register_file_cfg_fault_clear_w1c;
wire [7:0] fault_cause_unused_from_u_control_register_file_fault_cause;
wire [31:0] last_good_cmd_unused_from_u_control_register_file_last_good_cmd;
wire [15:0] timeout_counter_snapshot_unused_from_u_control_register_file_timeout_counter_snapshot;
wire request_launch;
wire request_ack;
assign cfg_fault_clear_w1c = mmio_valid & mmio_write & (mmio_addr == 8'h10) & mmio_wdata[0];

control_register_file u_control_register_file (
    .clk(clk),
    .rst_n(rst_n),
    .mmio_valid(mmio_valid),
    .mmio_write(mmio_write),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_rdata(mmio_rdata),
    .mmio_ready(mmio_ready),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_timeout_threshold(cfg_timeout_threshold),
    .cfg_request_seq_seed(cfg_request_seq_seed),
    .cfg_response_age_limit(cfg_response_age_limit),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_slew_enable(cfg_slew_enable),
    .cfg_slew_limit(cfg_slew_limit),
    .cfg_safe_selector(cfg_safe_selector),
    .cfg_fault_clear_w1c(cfg_fault_clear_w1c_unused_from_u_control_register_file_cfg_fault_clear_w1c),
    .fault_status(fault_status),
    .fault_cause(fault_cause_unused_from_u_control_register_file_fault_cause),
    .revision_id(revision_id),
    .last_good_cmd(last_good_cmd_unused_from_u_control_register_file_last_good_cmd),
    .timeout_counter_snapshot(timeout_counter_snapshot_unused_from_u_control_register_file_timeout_counter_snapshot),
    .request_id_snapshot(request_id_snapshot),
    .status_snapshot_valid(status_snapshot_valid)
);

request_framing_engine u_request_framing_engine (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_request_seq_seed(cfg_request_seq_seed),
    .request_launch(cfg_enable),
    .request_ack(fault_latched),
    .request_busy(request_busy),
    .request_id(request_id),
    .cmd_valid(cmd_valid),
    .cmd_data(cmd_data),
    .cmd_ready(cmd_ready)
);

response_validator u_response_validator (
    .clk(clk),
    .rst_n(rst_n),
    .rsp_valid(rsp_valid),
    .rsp_data(rsp_data),
    .rsp_ready(rsp_ready),
    .expected_request_id(request_id),
    .cfg_response_age_limit(cfg_response_age_limit),
    .cfg_mode(cfg_mode),
    .validated_response_valid(validated_response_valid),
    .validated_response_data(validated_response_data),
    .response_reject(response_reject),
    .response_reject_code(response_reject_code),
    .response_age_snapshot(response_age_snapshot)
);

safety_monitor u_safety_monitor (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_timeout_threshold(cfg_timeout_threshold),
    .request_outstanding(request_busy),
    .response_accepted(validated_response_valid),
    .response_reject(response_reject),
    .fault_clear(cfg_fault_clear_w1c),
    .safe_fallback(safe_fallback),
    .fault_latched(fault_latched),
    .fault_cause(fault_cause),
    .timeout_counter_snapshot(timeout_counter_snapshot),
    .fault_irq(fault_irq)
);

actuator_command_shaper u_actuator_command_shaper (
    .clk(clk),
    .rst_n(rst_n),
    .validated_response_valid(validated_response_valid),
    .validated_response_data(validated_response_data),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_slew_enable(cfg_slew_enable),
    .cfg_slew_limit(cfg_slew_limit),
    .safe_fallback(safe_fallback),
    .fault_latched(fault_latched),
    .actuator_cmd(actuator_cmd),
    .actuator_cmd_valid(actuator_cmd_valid),
    .last_good_cmd(last_good_cmd)
);

endmodule
