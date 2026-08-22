module adaptive_aero_control_top (
    clk,
    rst_n,
    mmio_addr,
    mmio_wdata,
    mmio_write,
    mmio_valid,
    mmio_rdata,
    mmio_ready,
    model_req_data,
    model_req_valid,
    model_req_ready,
    model_rsp_data,
    model_rsp_valid,
    model_rsp_ready,
    actuator_cmd_out,
    host_irq
);
input clk;
input rst_n;
input [7:0] mmio_addr;
input [31:0] mmio_wdata;
input mmio_write;
input mmio_valid;
output [31:0] mmio_rdata;
output mmio_ready;
output [127:0] model_req_data;
output model_req_valid;
input model_req_ready;
input [127:0] model_rsp_data;
input model_rsp_valid;
output model_rsp_ready;
output [31:0] actuator_cmd_out;
output host_irq;

wire [31:0] mmio_rdata_w;
wire mmio_ready_w;
wire [15:0] cfg_timeout_limit;
wire [1:0] cfg_seq_policy;
wire [3:0] cfg_control_mode_permit;
wire [7:0] cfg_act_min;
wire [7:0] cfg_act_max;
wire [7:0] cfg_safe_min;
wire [7:0] cfg_safe_max;
wire [3:0] cfg_irq_enable;
wire cfg_clear_sticky_faults;
wire cmd_valid;
wire [7:0] cmd_id;
wire [15:0] cmd_seq;
wire [15:0] cmd_age_ts;
wire [3:0] cmd_control_mode;
wire [7:0] cmd_act_pos;
wire [3:0] cmd_integrity;
wire accepted_event;
wire rejected_event;
wire stale_data_fault;
wire timeout_fault;
wire clamp_applied;
wire fallback_active;
wire [15:0] sequence_number_seen;
wire [15:0] watchdog_count;
wire [7:0] last_fault_code;
wire status_capture_valid;
wire [127:0] model_req_data_w;
wire model_req_valid_w;
wire model_rsp_ready_w;
wire [31:0] actuator_cmd_out_w;
wire host_irq_w;

assign mmio_rdata = mmio_rdata_w;
assign mmio_ready = mmio_ready_w;
assign model_req_data = model_req_data_w;
assign model_req_valid = model_req_valid_w;
assign model_rsp_ready = model_rsp_ready_w;
assign actuator_cmd_out = actuator_cmd_out_w;
assign host_irq = host_irq_w;

adaptive_aero_control_mmio u_mmio (
    .clk(clk),
    .rst_n(rst_n),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_write(mmio_write),
    .mmio_valid(mmio_valid),
    .mmio_rdata(mmio_rdata_w),
    .mmio_ready(mmio_ready_w),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_seq_policy(cfg_seq_policy),
    .cfg_control_mode_permit(cfg_control_mode_permit),
    .cfg_act_min(cfg_act_min),
    .cfg_act_max(cfg_act_max),
    .cfg_safe_min(cfg_safe_min),
    .cfg_safe_max(cfg_safe_max),
    .cfg_irq_enable(cfg_irq_enable),
    .cfg_clear_sticky_faults(cfg_clear_sticky_faults),
    .cmd_valid(cmd_valid),
    .cmd_id(cmd_id),
    .cmd_seq(cmd_seq),
    .cmd_age_ts(cmd_age_ts),
    .cmd_control_mode(cmd_control_mode),
    .cmd_act_pos(cmd_act_pos),
    .cmd_integrity(cmd_integrity),
    .accepted_event(accepted_event),
    .rejected_event(rejected_event),
    .stale_data_fault(stale_data_fault),
    .timeout_fault(timeout_fault),
    .clamp_applied(clamp_applied),
    .fallback_active(fallback_active),
    .sequence_number_seen(sequence_number_seen),
    .watchdog_count(watchdog_count),
    .last_fault_code(last_fault_code),
    .status_capture_valid(status_capture_valid)
);

adaptive_aero_safety_supervisor u_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_seq_policy(cfg_seq_policy),
    .cfg_control_mode_permit(cfg_control_mode_permit),
    .cfg_act_min(cfg_act_min),
    .cfg_act_max(cfg_act_max),
    .cfg_safe_min(cfg_safe_min),
    .cfg_safe_max(cfg_safe_max),
    .cfg_irq_enable(cfg_irq_enable),
    .cfg_clear_sticky_faults(cfg_clear_sticky_faults),
    .cmd_valid(cmd_valid),
    .cmd_id(cmd_id),
    .cmd_seq(cmd_seq),
    .cmd_age_ts(cmd_age_ts),
    .cmd_control_mode(cmd_control_mode),
    .cmd_act_pos(cmd_act_pos),
    .cmd_integrity(cmd_integrity),
    .accepted_event(accepted_event),
    .rejected_event(rejected_event),
    .stale_data_fault(stale_data_fault),
    .timeout_fault(timeout_fault),
    .clamp_applied(clamp_applied),
    .fallback_active(fallback_active),
    .sequence_number_seen(sequence_number_seen),
    .watchdog_count(watchdog_count),
    .last_fault_code(last_fault_code),
    .status_capture_valid(status_capture_valid),
    .actuator_cmd_out(actuator_cmd_out_w),
    .host_irq(host_irq_w)
);

assign model_req_data_w = {cmd_id, cmd_seq, cmd_age_ts, cmd_control_mode, cmd_act_pos, cmd_integrity, cfg_irq_enable, cfg_seq_policy, cfg_timeout_limit, cfg_act_min, cfg_act_max, cfg_safe_min, cfg_safe_max, 18'b0};
assign model_req_valid_w = cmd_valid;
assign model_rsp_ready_w = model_req_ready;

endmodule
