module adaptive_aero_control_top (
    clk,
    reset,
    reg_cs,
    reg_we,
    reg_re,
    reg_addr,
    reg_wdata,
    reg_rdata,
    model_req_valid,
    model_req_ready,
    model_req_data,
    model_rsp_valid,
    model_rsp_ready,
    model_rsp_data,
    actuator_cmd_valid,
    actuator_cmd_ready,
    actuator_cmd_data,
    fault_summary,
    heartbeat_status
);

input clk;
input reset;
input reg_cs;
input reg_we;
input reg_re;
input [3:0] reg_addr;
input [63:0] reg_wdata;
output [63:0] reg_rdata;
output model_req_valid;
input model_req_ready;
output [127:0] model_req_data;
input model_rsp_valid;
output model_rsp_ready;
input [127:0] model_rsp_data;
output actuator_cmd_valid;
input actuator_cmd_ready;
output [63:0] actuator_cmd_data;
output [7:0] fault_summary;
output [7:0] heartbeat_status;
wire cfg_enable;
wire [2:0] cfg_mode;
wire cfg_hold_last_valid;
wire cfg_fallback_enable;
wire cfg_heartbeat_enable;
wire cfg_seq_reset;
wire cfg_signed_clamp;
wire [2:0] cfg_queue_depth;
wire [7:0] cfg_service_flags;
wire [31:0] cfg_timeout_cycles;
wire [31:0] cfg_heartbeat_timeout_cycles;
wire [15:0] cfg_act0_min;
wire [15:0] cfg_act0_max;
wire [15:0] cfg_act1_min;
wire [15:0] cfg_act1_max;
wire [15:0] cfg_act2_min;
wire [15:0] cfg_act2_max;
wire [15:0] cfg_act3_min;
wire [15:0] cfg_act3_max;
wire [3:0] cfg_mode_context;
wire [11:0] cfg_operating_point_tag;
wire [15:0] cfg_velocity_tag;
wire [31:0] cfg_geometry_id;
wire [31:0] cfg_velocity_setpoint;
wire [31:0] cfg_age_basis;
wire [7:0] status_fault_summary;
wire [7:0] status_heartbeat;
wire [15:0] status_accepted_req_count;
wire [15:0] status_accepted_rsp_count;
wire [7:0] status_rejected_rsp_count;
wire [7:0] status_fallback_entry_count;
wire [127:0] req_data_int;
wire req_valid_int;
wire req_ready_int;
wire rsp_ready_int;
wire [63:0] act_data_int;
wire act_valid_int;
wire act_ready_int;

wire [63:0] actuator_cmd_data_unused_from_u_actuator_output_cmd_data;
wire actuator_cmd_valid_unused_from_u_actuator_output_cmd_valid;
wire act_valid_to_actuator;
wire [63:0] act_data_to_actuator;
wire act_ready_from_actuator;
assign model_req_valid = req_valid_int;
assign model_req_data = req_data_int;
assign model_rsp_ready = rsp_ready_int;
assign actuator_cmd_valid = act_valid_int;
assign actuator_cmd_data = act_data_int;
assign fault_summary = status_fault_summary;
assign heartbeat_status = status_heartbeat;

adaptive_aero_control_top_mmio u_mmio (
    .clk(clk),
    .reset(reset),
    .reg_cs(reg_cs),
    .reg_we(reg_we),
    .reg_re(reg_re),
    .reg_addr(reg_addr),
    .reg_wdata(reg_wdata),
    .reg_rdata(reg_rdata),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_hold_last_valid(cfg_hold_last_valid),
    .cfg_fallback_enable(cfg_fallback_enable),
    .cfg_heartbeat_enable(cfg_heartbeat_enable),
    .cfg_seq_reset(cfg_seq_reset),
    .cfg_signed_clamp(cfg_signed_clamp),
    .cfg_queue_depth(cfg_queue_depth),
    .cfg_service_flags(cfg_service_flags),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_heartbeat_timeout_cycles(cfg_heartbeat_timeout_cycles),
    .cfg_act0_min(cfg_act0_min),
    .cfg_act0_max(cfg_act0_max),
    .cfg_act1_min(cfg_act1_min),
    .cfg_act1_max(cfg_act1_max),
    .cfg_act2_min(cfg_act2_min),
    .cfg_act2_max(cfg_act2_max),
    .cfg_act3_min(cfg_act3_min),
    .cfg_act3_max(cfg_act3_max),
    .cfg_mode_context(cfg_mode_context),
    .cfg_operating_point_tag(cfg_operating_point_tag),
    .cfg_velocity_tag(cfg_velocity_tag),
    .cfg_geometry_id(cfg_geometry_id),
    .cfg_velocity_setpoint(cfg_velocity_setpoint),
    .cfg_age_basis(cfg_age_basis),
    .status_fault_summary(status_fault_summary),
    .status_heartbeat(status_heartbeat),
    .status_accepted_req_count(status_accepted_req_count),
    .status_accepted_rsp_count(status_accepted_rsp_count),
    .status_rejected_rsp_count(status_rejected_rsp_count),
    .status_fallback_entry_count(status_fallback_entry_count)
);

adaptive_aero_control_top_transport u_transport (
    .clk(clk),
    .reset(reset),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_hold_last_valid(cfg_hold_last_valid),
    .cfg_fallback_enable(cfg_fallback_enable),
    .cfg_heartbeat_enable(cfg_heartbeat_enable),
    .cfg_seq_reset(cfg_seq_reset),
    .cfg_signed_clamp(cfg_signed_clamp),
    .cfg_queue_depth(cfg_queue_depth),
    .cfg_service_flags(cfg_service_flags),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_heartbeat_timeout_cycles(cfg_heartbeat_timeout_cycles),
    .cfg_mode_context(cfg_mode_context),
    .cfg_operating_point_tag(cfg_operating_point_tag),
    .cfg_velocity_tag(cfg_velocity_tag),
    .cfg_geometry_id(cfg_geometry_id),
    .cfg_velocity_setpoint(cfg_velocity_setpoint),
    .cfg_age_basis(cfg_age_basis),
    .req_valid(req_valid_int),
    .req_ready(model_req_ready),
    .req_data(req_data_int),
    .rsp_valid(model_rsp_valid),
    .rsp_ready(rsp_ready_int),
    .rsp_data(model_rsp_data),
    .act_valid(act_valid_int),
    .act_ready(act_ready_int),
    .act_data(act_data_int),
    .fault_summary(status_fault_summary),
    .heartbeat_status(status_heartbeat),
    .accepted_req_count(status_accepted_req_count),
    .accepted_rsp_count(status_accepted_rsp_count),
    .rejected_rsp_count(status_rejected_rsp_count),
    .fallback_entry_count(status_fallback_entry_count)
);

adaptive_aero_control_top_actuator u_actuator (
    .clk(clk),
    .reset(reset),
    .cfg_signed_clamp(cfg_signed_clamp),
    .cfg_act0_min(cfg_act0_min),
    .cfg_act0_max(cfg_act0_max),
    .cfg_act1_min(cfg_act1_min),
    .cfg_act1_max(cfg_act1_max),
    .cfg_act2_min(cfg_act2_min),
    .cfg_act2_max(cfg_act2_max),
    .cfg_act3_min(cfg_act3_min),
    .cfg_act3_max(cfg_act3_max),
    .fallback_active(status_fault_summary[5]),
    .input_cmd_valid(act_valid_int),
    .input_cmd_ready(act_ready_int),
    .input_cmd_data(act_data_int),
    .output_cmd_valid(actuator_cmd_valid_unused_from_u_actuator_output_cmd_valid),
    .output_cmd_ready(actuator_cmd_ready),
    .output_cmd_data(actuator_cmd_data_unused_from_u_actuator_output_cmd_data)
);

endmodule
