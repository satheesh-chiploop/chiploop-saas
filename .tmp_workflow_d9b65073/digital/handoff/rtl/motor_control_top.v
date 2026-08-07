module motor_control_top (
    input         clk,
    input         reset_n,
    input         cfg_valid,
    output        cfg_ready,
    input  [15:0] cfg_addr,
    input         cfg_we,
    input  [31:0] cfg_wdata,
    output [31:0] cfg_rdata,
    output        cfg_rvalid,
    output        service_req_valid,
    input         service_req_ready,
    output [127:0] service_req_payload,
    input         service_rsp_valid,
    output        service_rsp_ready,
    input  [127:0] service_rsp_payload,
    output [31:0] actuator_cmd_o,
    output        actuator_cmd_valid,
    input         actuator_cmd_ready,
    output [31:0] status_o,
    input         motor_control_cfg_if_host_go_start,
    input         motor_control_cfg_if_host_clear_faults,
    input         motor_control_cfg_if_host_emergency_stop,
    input         motor_control_cfg_if_host_done_mode_latch,
    input  [15:0] motor_control_cfg_if_cfg_sequence_num,
    input  [15:0] motor_control_cfg_if_cfg_geometry_id,
    input  [31:0] motor_control_cfg_if_cfg_flow_condition,
    input  [15:0] motor_control_cfg_if_cfg_timeout_budget,
    input  [15:0] motor_control_cfg_if_cfg_freshness_limit,
    input  [15:0] motor_control_cfg_if_cfg_cmd_min,
    input  [15:0] motor_control_cfg_if_cfg_cmd_max,
    input  [7:0] motor_control_cfg_if_cfg_policy,
    input  [31:0] motor_control_cfg_if_cfg_safe_fallback_cfg,
    output [31:0] motor_control_cfg_if_status_i,
    output        motor_control_request_packer_launch_req,
    output        motor_control_request_packer_busy_i,
    output [15:0] motor_control_request_packer_cfg_sequence_num,
    output [15:0] motor_control_request_packer_cfg_geometry_id,
    output [31:0] motor_control_request_packer_cfg_flow_condition,
    output [15:0] motor_control_request_packer_cfg_timeout_budget,
    output [15:0] motor_control_request_packer_cfg_freshness_limit,
    output [15:0] motor_control_request_packer_cfg_cmd_min,
    output [15:0] motor_control_request_packer_cfg_cmd_max,
    output [7:0] motor_control_request_packer_cfg_policy,
    input         motor_control_request_packer_request_valid,
    output        motor_control_request_packer_request_ready,
    input  [127:0] motor_control_request_packer_request_payload,
    output        motor_control_response_guard_request_accepted,
    output [127:0] motor_control_response_guard_request_payload,
    output        motor_control_response_guard_busy_i,
    output [15:0] motor_control_response_guard_cfg_sequence_num,
    output [15:0] motor_control_response_guard_cfg_timeout_budget,
    output [15:0] motor_control_response_guard_cfg_freshness_limit,
    output [15:0] motor_control_response_guard_cfg_cmd_min,
    output [15:0] motor_control_response_guard_cfg_cmd_max,
    output [31:0] motor_control_response_guard_cfg_safe_fallback_cfg,
    output        motor_control_response_guard_host_clear_faults,
    output        motor_control_response_guard_host_emergency_stop,
    output        motor_control_response_guard_host_done_mode_latch,
    input         motor_control_response_guard_busy_o,
    input         motor_control_response_guard_done_o
);

wire cfg_ready_i;
wire [31:0] cfg_rdata_i;
wire cfg_rvalid_i;
wire host_go_start_i;
wire host_clear_faults_i;
wire host_emergency_stop_i;
wire host_done_mode_latch_i;
wire [15:0] cfg_sequence_num_i;
wire [15:0] cfg_geometry_id_i;
wire [31:0] cfg_flow_condition_i;
wire [15:0] cfg_timeout_budget_i;
wire [15:0] cfg_freshness_limit_i;
wire [15:0] cfg_cmd_min_i;
wire [15:0] cfg_cmd_max_i;
wire [7:0] cfg_policy_i;
wire [31:0] cfg_safe_fallback_cfg_i;
wire [31:0] status_i;
assign cfg_ready = cfg_ready_i;
assign cfg_rdata = cfg_rdata_i;
assign cfg_rvalid = cfg_rvalid_i;
assign motor_control_cfg_if_status_i = status_i;
assign service_rsp_ready = 1'b1;
assign actuator_cmd_o = motor_control_response_guard_actuator_cmd_o;
assign actuator_cmd_valid = motor_control_response_guard_actuator_cmd_valid;

wire launch_req_i;
wire busy_i;
wire [15:0] req_seq_i;
wire [15:0] req_geo_i;
wire [31:0] req_flow_i;
wire [15:0] req_to_i;
wire [15:0] req_fresh_i;
wire [15:0] req_min_i;
wire [15:0] req_max_i;
wire [7:0] req_pol_i;
wire req_valid_i;
wire [127:0] req_payload_i;
assign motor_control_request_packer_launch_req = launch_req_i;
assign motor_control_request_packer_busy_i = busy_i;
assign motor_control_request_packer_cfg_sequence_num = req_seq_i;
assign motor_control_request_packer_cfg_geometry_id = req_geo_i;
assign motor_control_request_packer_cfg_flow_condition = req_flow_i;
assign motor_control_request_packer_cfg_timeout_budget = req_to_i;
assign motor_control_request_packer_cfg_freshness_limit = req_fresh_i;
assign motor_control_request_packer_cfg_cmd_min = req_min_i;
assign motor_control_request_packer_cfg_cmd_max = req_max_i;
assign motor_control_request_packer_cfg_policy = req_pol_i;
assign motor_control_request_packer_request_ready = service_req_ready;

assign service_req_valid = req_valid_i;
assign service_req_payload = req_payload_i;

wire request_accepted_i;
wire [127:0] rsp_req_payload_i;
wire guard_busy_i;
wire [15:0] guard_seq_i;
wire [15:0] guard_to_i;
wire [15:0] guard_fresh_i;
wire [15:0] guard_min_i;
wire [15:0] guard_max_i;
wire [31:0] guard_fallback_i;
wire guard_clear_i;
wire guard_estop_i;
wire guard_done_latch_i;
wire guard_busy_o_i;
wire guard_done_o_i;
wire [31:0] guard_status_i;
wire [31:0] motor_control_response_guard_actuator_cmd_o;
wire motor_control_response_guard_actuator_cmd_valid;

wire guard_busy_o_i_unused_from_u_motor_control_response_guard_busy_o;
wire guard_done_o_i_unused_from_u_motor_control_response_guard_done_o;
wire [127:0] req_payload_i_unused_from_u_motor_control_request_packer_request_payload;
wire req_valid_i_unused_from_u_motor_control_request_packer_request_valid;
wire service_rsp_ready_unused_from_u_motor_control_response_guard_service_rsp_ready;
assign motor_control_response_guard_request_accepted = request_accepted_i;
assign motor_control_response_guard_request_payload = rsp_req_payload_i;
assign motor_control_response_guard_busy_i = guard_busy_i;
assign motor_control_response_guard_cfg_sequence_num = guard_seq_i;
assign motor_control_response_guard_cfg_timeout_budget = guard_to_i;
assign motor_control_response_guard_cfg_freshness_limit = guard_fresh_i;
assign motor_control_response_guard_cfg_cmd_min = guard_min_i;
assign motor_control_response_guard_cfg_cmd_max = guard_max_i;
assign motor_control_response_guard_cfg_safe_fallback_cfg = guard_fallback_i;
assign motor_control_response_guard_host_clear_faults = guard_clear_i;
assign motor_control_response_guard_host_emergency_stop = guard_estop_i;
assign motor_control_response_guard_host_done_mode_latch = guard_done_latch_i;
assign status_o = guard_status_i;

assign launch_req_i = host_go_start_i;
assign busy_i = guard_busy_o_i;
assign req_seq_i = cfg_sequence_num_i;
assign req_geo_i = cfg_geometry_id_i;
assign req_flow_i = cfg_flow_condition_i;
assign req_to_i = cfg_timeout_budget_i;
assign req_fresh_i = cfg_freshness_limit_i;
assign req_min_i = cfg_cmd_min_i;
assign req_max_i = cfg_cmd_max_i;
assign req_pol_i = cfg_policy_i;
assign req_valid_i = motor_control_request_packer_request_valid;
assign req_payload_i = motor_control_request_packer_request_payload;
assign request_accepted_i = req_valid_i & service_req_ready;
assign rsp_req_payload_i = req_payload_i;
assign guard_busy_i = busy_i;
assign guard_seq_i = cfg_sequence_num_i;
assign guard_to_i = cfg_timeout_budget_i;
assign guard_fresh_i = cfg_freshness_limit_i;
assign guard_min_i = cfg_cmd_min_i;
assign guard_max_i = cfg_cmd_max_i;
assign guard_fallback_i = cfg_safe_fallback_cfg_i;
assign guard_clear_i = host_clear_faults_i;
assign guard_estop_i = host_emergency_stop_i;
assign guard_done_latch_i = host_done_mode_latch_i;
assign guard_busy_o_i = motor_control_response_guard_busy_o;
assign guard_done_o_i = motor_control_response_guard_done_o;

motor_control_cfg_if u_motor_control_cfg_if (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_valid(cfg_valid),
    .cfg_ready(cfg_ready_i),
    .cfg_addr(cfg_addr),
    .cfg_we(cfg_we),
    .cfg_wdata(cfg_wdata),
    .cfg_rdata(cfg_rdata_i),
    .cfg_rvalid(cfg_rvalid_i),
    .host_go_start(host_go_start_i),
    .host_clear_faults(host_clear_faults_i),
    .host_emergency_stop(host_emergency_stop_i),
    .host_done_mode_latch(host_done_mode_latch_i),
    .cfg_sequence_num(cfg_sequence_num_i),
    .cfg_geometry_id(cfg_geometry_id_i),
    .cfg_flow_condition(cfg_flow_condition_i),
    .cfg_timeout_budget(cfg_timeout_budget_i),
    .cfg_freshness_limit(cfg_freshness_limit_i),
    .cfg_cmd_min(cfg_cmd_min_i),
    .cfg_cmd_max(cfg_cmd_max_i),
    .cfg_policy(cfg_policy_i),
    .cfg_safe_fallback_cfg(cfg_safe_fallback_cfg_i),
    .status_i(status_i)
);

motor_control_request_packer u_motor_control_request_packer (
    .clk(clk),
    .reset_n(reset_n),
    .launch_req(launch_req_i),
    .busy_i(busy_i),
    .cfg_sequence_num(req_seq_i),
    .cfg_geometry_id(req_geo_i),
    .cfg_flow_condition(req_flow_i),
    .cfg_timeout_budget(req_to_i),
    .cfg_freshness_limit(req_fresh_i),
    .cfg_cmd_min(req_min_i),
    .cfg_cmd_max(req_max_i),
    .cfg_policy(req_pol_i),
    .request_valid(req_valid_i_unused_from_u_motor_control_request_packer_request_valid),
    .request_ready(service_req_ready),
    .request_payload(req_payload_i_unused_from_u_motor_control_request_packer_request_payload)
);

motor_control_response_guard u_motor_control_response_guard (
    .clk(clk),
    .reset_n(reset_n),
    .request_accepted(request_accepted_i),
    .request_payload(rsp_req_payload_i),
    .service_rsp_valid(service_rsp_valid),
    .service_rsp_ready(service_rsp_ready_unused_from_u_motor_control_response_guard_service_rsp_ready),
    .service_rsp_payload(service_rsp_payload),
    .busy_i(guard_busy_i),
    .cfg_sequence_num(guard_seq_i),
    .cfg_timeout_budget(guard_to_i),
    .cfg_freshness_limit(guard_fresh_i),
    .cfg_cmd_min(guard_min_i),
    .cfg_cmd_max(guard_max_i),
    .cfg_safe_fallback_cfg(guard_fallback_i),
    .host_clear_faults(guard_clear_i),
    .host_emergency_stop(guard_estop_i),
    .host_done_mode_latch(guard_done_latch_i),
    .actuator_cmd_o(motor_control_response_guard_actuator_cmd_o),
    .actuator_cmd_valid(motor_control_response_guard_actuator_cmd_valid),
    .actuator_cmd_ready(actuator_cmd_ready),
    .busy_o(guard_busy_o_i_unused_from_u_motor_control_response_guard_busy_o),
    .done_o(guard_done_o_i_unused_from_u_motor_control_response_guard_done_o),
    .status_o(guard_status_i)
);

endmodule
