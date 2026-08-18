module adaptive_aero_control_top (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_we_i,
    wb_stb_i,
    wb_cyc_i,
    wb_ack_o,
    wb_err_o,
    model_req_desc_o,
    model_req_valid_o,
    model_req_ready_i,
    model_rsp_desc_i,
    model_rsp_valid_i,
    model_rsp_ready_o,
    actuator_cmd_o,
    actuator_cmd_valid_o,
    fault_o,
    irq_o
);

input clk;
input reset_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input wb_we_i;
input wb_stb_i;
input wb_cyc_i;
output wb_ack_o;
output wb_err_o;
output [63:0] model_req_desc_o;
output model_req_valid_o;
input model_req_ready_i;
input [63:0] model_rsp_desc_i;
input model_rsp_valid_i;
output model_rsp_ready_o;
output [15:0] actuator_cmd_o;
output actuator_cmd_valid_o;
output fault_o;
output irq_o;
wire [15:0] cfg_oper_en_min;
wire [15:0] cfg_oper_en_max;
wire [31:0] cfg_timeout_cycles;
wire [15:0] cfg_clamp_min;
wire [15:0] cfg_clamp_max;
wire cfg_rate_limit_en;
wire [15:0] cfg_rate_limit_step;
wire [15:0] cfg_fallback_cmd;
wire cfg_force_safe_mode;
wire cfg_allow_multi_outstanding;
wire cfg_request_issue;
wire [7:0] cfg_request_id;
wire [15:0] cfg_geometry_handle;
wire [15:0] cfg_flow_handle;
wire [31:0] cfg_timestamp;
wire [3:0] cfg_command_mode;
wire [7:0] cfg_status_flags;
wire [31:0] reg_version;
wire [31:0] reg_capabilities;
wire [7:0] reg_state;
wire [15:0] reg_fault_summary;
wire [7:0] reg_outstanding_req_id;
wire [7:0] reg_response_req_id;
wire [15:0] reg_last_accepted_cmd;
wire reg_pending;
wire reg_response_received;
wire reg_stale_reject;
wire reg_timeout_expired;
wire reg_clamp_active;
wire reg_fallback_active;
wire reg_envelope_violation;
wire reg_service_error;
wire reg_irq_pulse;
wire [15:0] last_accepted_cmd_o;
wire [15:0] selected_cmd_o;
wire selected_cmd_valid_o;
wire adaptive_aero_control_top_request_fsm_reg_stale_reject;
adaptive_aero_control_top_mmio u_mmio (
    .clk(clk),
    .reset_n(reset_n),
    .wb_adr_i(wb_adr_i),
    .wb_dat_i(wb_dat_i),
    .wb_dat_o(wb_dat_o),
    .wb_we_i(wb_we_i),
    .wb_stb_i(wb_stb_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_ack_o(wb_ack_o),
    .wb_err_o(wb_err_o),
    .cfg_oper_en_min(cfg_oper_en_min),
    .cfg_oper_en_max(cfg_oper_en_max),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_clamp_min(cfg_clamp_min),
    .cfg_clamp_max(cfg_clamp_max),
    .cfg_rate_limit_en(cfg_rate_limit_en),
    .cfg_rate_limit_step(cfg_rate_limit_step),
    .cfg_fallback_cmd(cfg_fallback_cmd),
    .cfg_force_safe_mode(cfg_force_safe_mode),
    .cfg_allow_multi_outstanding(cfg_allow_multi_outstanding),
    .cfg_request_issue(cfg_request_issue),
    .cfg_request_id(cfg_request_id),
    .cfg_geometry_handle(cfg_geometry_handle),
    .cfg_flow_handle(cfg_flow_handle),
    .cfg_timestamp(cfg_timestamp),
    .cfg_command_mode(cfg_command_mode),
    .cfg_status_flags(cfg_status_flags),
    .reg_version(reg_version),
    .reg_capabilities(reg_capabilities),
    .reg_state(reg_state),
    .reg_fault_summary(reg_fault_summary),
    .reg_outstanding_req_id(reg_outstanding_req_id),
    .reg_response_req_id(reg_response_req_id),
    .reg_last_accepted_cmd(reg_last_accepted_cmd),
    .reg_pending(reg_pending),
    .reg_response_received(reg_response_received),
    .reg_stale_reject(reg_stale_reject),
    .reg_timeout_expired(reg_timeout_expired),
    .reg_clamp_active(reg_clamp_active),
    .reg_fallback_active(reg_fallback_active),
    .reg_envelope_violation(reg_envelope_violation),
    .reg_service_error(reg_service_error),
    .reg_irq_pulse(reg_irq_pulse)
);

adaptive_aero_control_top_request_fsm u_fsm (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_request_issue(cfg_request_issue),
    .cfg_allow_multi_outstanding(cfg_allow_multi_outstanding),
    .cfg_request_id(cfg_request_id),
    .cfg_geometry_handle(cfg_geometry_handle),
    .cfg_flow_handle(cfg_flow_handle),
    .cfg_timestamp(cfg_timestamp),
    .cfg_command_mode(cfg_command_mode),
    .cfg_status_flags(cfg_status_flags),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_force_safe_mode(cfg_force_safe_mode),
    .cfg_oper_en_min(cfg_oper_en_min),
    .cfg_oper_en_max(cfg_oper_en_max),
    .model_req_desc_o(model_req_desc_o),
    .model_req_valid_o(model_req_valid_o),
    .model_req_ready_i(model_req_ready_i),
    .model_rsp_desc_i(model_rsp_desc_i),
    .model_rsp_valid_i(model_rsp_valid_i),
    .model_rsp_ready_o(model_rsp_ready_o),
    .reg_state(reg_state),
    .reg_fault_summary(reg_fault_summary),
    .reg_outstanding_req_id(reg_outstanding_req_id),
    .reg_response_req_id(reg_response_req_id),
    .reg_pending(reg_pending),
    .reg_response_received(reg_response_received),
    .reg_stale_reject(reg_stale_reject),
    .reg_timeout_expired(reg_timeout_expired),
    .reg_envelope_violation(reg_envelope_violation),
    .reg_service_error(reg_service_error),
    .reg_fallback_active(reg_fallback_active),
    .reg_irq_pulse(reg_irq_pulse),
    .selected_cmd_o(),
    .selected_cmd_valid_o()
);

adaptive_aero_control_top_actuator_safety u_safety (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_clamp_min(cfg_clamp_min),
    .cfg_clamp_max(cfg_clamp_max),
    .cfg_rate_limit_en(cfg_rate_limit_en),
    .cfg_rate_limit_step(cfg_rate_limit_step),
    .cfg_fallback_cmd(cfg_fallback_cmd),
    .reg_fallback_active(reg_fallback_active),
    .reg_envelope_violation(reg_envelope_violation),
    .reg_timeout_expired(reg_timeout_expired),
    .reg_stale_reject(reg_stale_reject),
    .reg_service_error(reg_service_error),
    .reg_pending(reg_pending),
    .selected_cmd_o(16'h0000),
    .selected_cmd_valid_o(1'b0),
    .last_accepted_cmd_o(last_accepted_cmd_o),
    .actuator_cmd_o(actuator_cmd_o),
    .actuator_cmd_valid_o(actuator_cmd_valid_o),
    .reg_clamp_active(reg_clamp_active),
    .reg_last_accepted_cmd(reg_last_accepted_cmd)
);

assign fault_o = reg_fallback_active;
assign irq_o = reg_irq_pulse;

endmodule
