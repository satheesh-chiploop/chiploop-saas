module adaptive_aero_control_top (
    clk,
    reset,
    wb_ctrl_if_adr_i,
    wb_ctrl_if_dat_i,
    wb_ctrl_if_dat_o,
    wb_ctrl_if_cyc_i,
    wb_ctrl_if_stb_i,
    wb_ctrl_if_we_i,
    wb_ctrl_if_sel_i,
    wb_ctrl_if_ack_o,
    wb_ctrl_if_err_o,
    req_stream_data,
    req_stream_valid,
    req_stream_ready,
    rsp_stream_data,
    rsp_stream_valid,
    rsp_stream_ready,
    actuator_cmd_pos,
    actuator_cmd_rate,
    actuator_cmd_valid,
    irq_o
);

input clk;
input reset;
input [7:0] wb_ctrl_if_adr_i;
input [31:0] wb_ctrl_if_dat_i;
output [31:0] wb_ctrl_if_dat_o;
input wb_ctrl_if_cyc_i;
input wb_ctrl_if_stb_i;
input wb_ctrl_if_we_i;
input [3:0] wb_ctrl_if_sel_i;
output wb_ctrl_if_ack_o;
output wb_ctrl_if_err_o;
output [127:0] req_stream_data;
output req_stream_valid;
input req_stream_ready;
input [127:0] rsp_stream_data;
input rsp_stream_valid;
output rsp_stream_ready;
output [15:0] actuator_cmd_pos;
output [15:0] actuator_cmd_rate;
output actuator_cmd_valid;
output irq_o;
wire cfg_enable;
wire [2:0] cfg_mode_select;
wire [7:0] cfg_request_sequence;
wire [15:0] cfg_timeout_limit;
wire [7:0] cfg_stale_limit;
wire [15:0] cfg_velocity_mps;
wire [15:0] cfg_velocity_min_mps;
wire [15:0] cfg_velocity_max_mps;
wire [15:0] cfg_actuator_min;
wire [15:0] cfg_actuator_max;
wire [15:0] cfg_actuator_safe_pos;
wire [7:0] cfg_interrupt_mask;
wire cfg_clear_faults;
wire status_rsp_accepted;
wire status_rsp_rejected;
wire status_stale_event;
wire status_timeout_event;
wire status_clamp_event;
wire status_safe_inhibit;
wire status_fault_latched;
wire [15:0] fault_status;
wire [7:0] fault_code;
wire [15:0] accepted_rsp_count;
wire [15:0] rejected_rsp_count;
wire [15:0] stale_event_count;
wire [15:0] timeout_event_count;
wire [15:0] clamp_event_count;
wire [7:0] last_good_sequence;
wire [7:0] last_fault_code;
wire [31:0] identification;
wire [127:0] request_packet_shadow;
wire [31:0] response_metadata_shadow;
wire [127:0] request_packet;
wire request_valid;
wire [127:0] response_packet_shadow;
wire response_accepted;
wire response_rejected;
wire response_stale;
wire response_timeout;
wire response_clamp_required;
wire [7:0] response_sequence;
wire [15:0] response_drag_summary;
wire [15:0] response_lift_summary;
wire [15:0] response_recommendation;
wire [31:0] response_metadata;
wire response_checksum_ok;

wire request_coherent;
adaptive_aero_control_registers u_regs (
    .clk(clk),
    .reset(reset),
    .wb_adr_i(wb_ctrl_if_adr_i),
    .wb_dat_i(wb_ctrl_if_dat_i),
    .wb_dat_o(wb_ctrl_if_dat_o),
    .wb_cyc_i(wb_ctrl_if_cyc_i),
    .wb_stb_i(wb_ctrl_if_stb_i),
    .wb_we_i(wb_ctrl_if_we_i),
    .wb_sel_i(wb_ctrl_if_sel_i),
    .wb_ack_o(wb_ctrl_if_ack_o),
    .wb_err_o(wb_ctrl_if_err_o),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_request_sequence(cfg_request_sequence),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_stale_limit(cfg_stale_limit),
    .cfg_velocity_mps(cfg_velocity_mps),
    .cfg_velocity_min_mps(cfg_velocity_min_mps),
    .cfg_velocity_max_mps(cfg_velocity_max_mps),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_actuator_safe_pos(cfg_actuator_safe_pos),
    .cfg_interrupt_mask(cfg_interrupt_mask),
    .cfg_clear_faults(cfg_clear_faults),
    .status_rsp_accepted(status_rsp_accepted),
    .status_rsp_rejected(status_rsp_rejected),
    .status_stale_event(status_stale_event),
    .status_timeout_event(status_timeout_event),
    .status_clamp_event(status_clamp_event),
    .status_safe_inhibit(status_safe_inhibit),
    .status_fault_latched(status_fault_latched),
    .fault_status(fault_status),
    .fault_code(fault_code),
    .accepted_rsp_count(accepted_rsp_count),
    .rejected_rsp_count(rejected_rsp_count),
    .stale_event_count(stale_event_count),
    .timeout_event_count(timeout_event_count),
    .clamp_event_count(clamp_event_count),
    .last_good_sequence(last_good_sequence),
    .last_fault_code(last_fault_code),
    .identification(identification),
    .request_packet_shadow(request_packet_shadow),
    .response_metadata_shadow(response_metadata_shadow)
);

adaptive_aero_control_request_packager u_req (
    .clk(clk),
    .reset(reset),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_request_sequence(cfg_request_sequence),
    .cfg_velocity_mps(cfg_velocity_mps),
    .cfg_velocity_min_mps(cfg_velocity_min_mps),
    .cfg_velocity_max_mps(cfg_velocity_max_mps),
    .request_packet(request_packet),
    .request_valid(request_valid),
    .request_ready(req_stream_ready),
    .request_coherent(cfg_enable),
    .request_packet_shadow(request_packet_shadow)
);

adaptive_aero_control_response_parser u_rsp (
    .clk(clk),
    .reset(reset),
    .rsp_data(rsp_stream_data),
    .rsp_valid(rsp_stream_valid),
    .rsp_ready(rsp_stream_ready),
    .cfg_request_sequence(cfg_request_sequence),
    .cfg_stale_limit(cfg_stale_limit),
    .cfg_velocity_min_mps(cfg_velocity_min_mps),
    .cfg_velocity_max_mps(cfg_velocity_max_mps),
    .response_accepted(response_accepted),
    .response_rejected(response_rejected),
    .response_stale(response_stale),
    .response_timeout(response_timeout),
    .response_clamp_required(response_clamp_required),
    .response_sequence(response_sequence),
    .response_drag_summary(response_drag_summary),
    .response_lift_summary(response_lift_summary),
    .response_recommendation(response_recommendation),
    .response_metadata(response_metadata),
    .response_checksum_ok(response_checksum_ok),
    .response_packet_shadow(response_packet_shadow)
);

adaptive_aero_control_supervisor u_sup (
    .clk(clk),
    .reset(reset),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_request_sequence(cfg_request_sequence),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_stale_limit(cfg_stale_limit),
    .cfg_velocity_mps(cfg_velocity_mps),
    .cfg_velocity_min_mps(cfg_velocity_min_mps),
    .cfg_velocity_max_mps(cfg_velocity_max_mps),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_actuator_safe_pos(cfg_actuator_safe_pos),
    .cfg_interrupt_mask(cfg_interrupt_mask),
    .cfg_clear_faults(cfg_clear_faults),
    .response_accepted(response_accepted),
    .response_rejected(response_rejected),
    .response_stale(response_stale),
    .response_timeout(response_timeout),
    .response_clamp_required(response_clamp_required),
    .response_sequence(response_sequence),
    .response_drag_summary(response_drag_summary),
    .response_lift_summary(response_lift_summary),
    .response_recommendation(response_recommendation),
    .response_metadata(response_metadata),
    .accepted_rsp_count(accepted_rsp_count),
    .rejected_rsp_count(rejected_rsp_count),
    .stale_event_count(stale_event_count),
    .timeout_event_count(timeout_event_count),
    .clamp_event_count(clamp_event_count),
    .last_good_sequence(last_good_sequence),
    .last_fault_code(last_fault_code),
    .fault_status(fault_status),
    .fault_code(fault_code),
    .status_rsp_accepted(status_rsp_accepted),
    .status_rsp_rejected(status_rsp_rejected),
    .status_stale_event(status_stale_event),
    .status_timeout_event(status_timeout_event),
    .status_clamp_event(status_clamp_event),
    .status_safe_inhibit(status_safe_inhibit),
    .status_fault_latched(status_fault_latched),
    .actuator_cmd_pos(actuator_cmd_pos),
    .actuator_cmd_rate(actuator_cmd_rate),
    .actuator_cmd_valid(actuator_cmd_valid),
    .irq_o(irq_o)
);

assign req_stream_data = request_packet;
assign req_stream_valid = request_valid;

assign response_metadata_shadow = response_metadata;

endmodule
