module adaptive_aero_control_top (
    clk,
    rst_n,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    cfg_valid,
    cfg_write,
    cfg_ready,
    model_req_valid,
    model_req_ready,
    model_req_data,
    model_rsp_valid,
    model_rsp_ready,
    model_rsp_data,
    external_fault_i,
    actuator_out_valid,
    actuator_out_cmd,
    status_busy,
    status_accepted,
    status_rejected_stale,
    status_rejected_seq,
    status_timeout,
    status_fallback_active,
    status_clamped,
    status_fault_summary
);

input clk;
input rst_n;
input [63:0] cfg_addr;
input [63:0] cfg_wdata;
output [63:0] cfg_rdata;
input cfg_valid;
input cfg_write;
output cfg_ready;
output model_req_valid;
input model_req_ready;
output [63:0] model_req_data;
input model_rsp_valid;
output model_rsp_ready;
input [63:0] model_rsp_data;
input external_fault_i;
output actuator_out_valid;
output [63:0] actuator_out_cmd;
output status_busy;
output status_accepted;
output status_rejected_stale;
output status_rejected_seq;
output status_timeout;
output status_fallback_active;
output status_clamped;
output status_fault_summary;
wire cfg_enable;
wire cfg_safe_fallback_select;
wire [63:0] cfg_max_cmd_pos;
wire [63:0] cfg_min_cmd_pos;
wire [63:0] cfg_max_cmd_rate;
wire [63:0] cfg_stale_timeout_cycles;
wire [63:0] cfg_response_timeout_cycles;
wire [63:0] cfg_sequence_expected;
wire [63:0] cfg_stream_velocity_setpoint;
wire [63:0] cfg_fault_mask;
wire status_busy_i;
wire status_accepted_i;
wire status_rejected_stale_i;
wire status_rejected_seq_i;
wire status_timeout_i;
wire status_fallback_active_i;
wire status_clamped_i;
wire status_fault_summary_i;

adaptive_aero_control_top_mmio u_mmio (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_addr(cfg_addr),
    .cfg_wdata(cfg_wdata),
    .cfg_rdata(cfg_rdata),
    .cfg_valid(cfg_valid),
    .cfg_write(cfg_write),
    .cfg_ready(cfg_ready),
    .cfg_enable(cfg_enable),
    .cfg_safe_fallback_select(cfg_safe_fallback_select),
    .cfg_max_cmd_pos(cfg_max_cmd_pos),
    .cfg_min_cmd_pos(cfg_min_cmd_pos),
    .cfg_max_cmd_rate(cfg_max_cmd_rate),
    .cfg_stale_timeout_cycles(cfg_stale_timeout_cycles),
    .cfg_response_timeout_cycles(cfg_response_timeout_cycles),
    .cfg_sequence_expected(cfg_sequence_expected),
    .cfg_stream_velocity_setpoint(cfg_stream_velocity_setpoint),
    .cfg_fault_mask(cfg_fault_mask),
    .status_busy_i(status_busy_i),
    .status_accepted_i(status_accepted_i),
    .status_rejected_stale_i(status_rejected_stale_i),
    .status_rejected_seq_i(status_rejected_seq_i),
    .status_timeout_i(status_timeout_i),
    .status_fallback_active_i(status_fallback_active_i),
    .status_clamped_i(status_clamped_i),
    .status_fault_summary_i(status_fault_summary_i)
);

adaptive_aero_control_top_supervisor u_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_safe_fallback_select(cfg_safe_fallback_select),
    .cfg_max_cmd_pos(cfg_max_cmd_pos),
    .cfg_min_cmd_pos(cfg_min_cmd_pos),
    .cfg_max_cmd_rate(cfg_max_cmd_rate),
    .cfg_stale_timeout_cycles(cfg_stale_timeout_cycles),
    .cfg_response_timeout_cycles(cfg_response_timeout_cycles),
    .cfg_sequence_expected(cfg_sequence_expected),
    .cfg_stream_velocity_setpoint(cfg_stream_velocity_setpoint),
    .cfg_fault_mask(cfg_fault_mask),
    .model_req_ready(model_req_ready),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_req_valid(model_req_valid),
    .model_req_data(model_req_data),
    .model_rsp_ready(model_rsp_ready),
    .external_fault_i(external_fault_i),
    .actuator_out_valid(actuator_out_valid),
    .actuator_out_cmd(actuator_out_cmd),
    .status_busy_o(status_busy_i),
    .status_accepted_o(status_accepted_i),
    .status_rejected_stale_o(status_rejected_stale_i),
    .status_rejected_seq_o(status_rejected_seq_i),
    .status_timeout_o(status_timeout_i),
    .status_fallback_active_o(status_fallback_active_i),
    .status_clamped_o(status_clamped_i),
    .status_fault_summary_o(status_fault_summary_i)
);

assign status_busy = status_busy_i;
assign status_accepted = status_accepted_i;
assign status_rejected_stale = status_rejected_stale_i;
assign status_rejected_seq = status_rejected_seq_i;
assign status_timeout = status_timeout_i;
assign status_fallback_active = status_fallback_active_i;
assign status_clamped = status_clamped_i;
assign status_fault_summary = status_fault_summary_i;

endmodule
