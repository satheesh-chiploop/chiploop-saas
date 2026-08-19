module adaptive_aero_control_top (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_sel_i,
    wb_we_i,
    wb_stb_i,
    wb_cyc_i,
    wb_ack_o,
    wb_err_o,
    stream_req_valid_o,
    stream_req_ready_i,
    stream_req_data_o,
    stream_rsp_valid_i,
    stream_rsp_ready_o,
    stream_rsp_data_i,
    actuator_cmd_o,
    irq_o,
    uart_tx_o,
    uart_rx_i
);
input clk;
input reset_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input [3:0] wb_sel_i;
input wb_we_i;
input wb_stb_i;
input wb_cyc_i;
output wb_ack_o;
output wb_err_o;
output stream_req_valid_o;
input stream_req_ready_i;
output [127:0] stream_req_data_o;
input stream_rsp_valid_i;
output stream_rsp_ready_o;
input [127:0] stream_rsp_data_i;
output [31:0] actuator_cmd_o;
output irq_o;
output uart_tx_o;
input uart_rx_i;
wire cfg_enable;
wire cfg_arm;
wire [1:0] cfg_mode;
wire [31:0] cfg_velocity_setpoint;
wire [31:0] cfg_clamp_min;
wire [31:0] cfg_clamp_max;
wire [15:0] cfg_timeout_threshold;
wire [15:0] cfg_sequence_counter;
wire [7:0] cfg_fault_clear_w1c;
wire [3:0] irq_enable;
wire [15:0] last_seen_sequence;
wire fresh;
wire stale;
wire timeout;
wire [7:0] fault_sticky;
wire allow_command;
wire [3:0] irq_status;
wire response_valid;
wire [15:0] response_sequence;
wire response_fresh;
wire [31:0] response_drag;
wire [31:0] response_lift;
wire [7:0] response_status_flags;
wire response_ready_pulse;
wire [31:0] status_actuator_cmd;
wire [127:0] stream_req_data_int;
wire stream_req_valid_int;
wire stream_rsp_ready_int;
wire [31:0] actuator_cmd_int;
wire irq_int;
wire [3:0] irq_status_int;
wire wb_ack_int;
wire wb_err_int;
wire [31:0] wb_dat_int;
wire request_due;
wire [31:0] local_timestamp;
wire [15:0] request_id;
wire [31:0] actuator_cmd;
adaptive_aero_control_csr_mmio u_csr (
    .clk(clk),
    .reset_n(reset_n),
    .wb_adr_i(wb_adr_i),
    .wb_dat_i(wb_dat_i),
    .wb_dat_o(wb_dat_int),
    .wb_sel_i(wb_sel_i),
    .wb_we_i(wb_we_i),
    .wb_stb_i(wb_stb_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_ack_o(wb_ack_int),
    .wb_err_o(wb_err_int),
    .cfg_enable_o(cfg_enable),
    .cfg_arm_o(cfg_arm),
    .cfg_mode_o(cfg_mode),
    .cfg_velocity_setpoint_o(cfg_velocity_setpoint),
    .cfg_clamp_min_o(cfg_clamp_min),
    .cfg_clamp_max_o(cfg_clamp_max),
    .cfg_timeout_threshold_o(cfg_timeout_threshold),
    .cfg_sequence_counter_o(cfg_sequence_counter),
    .cfg_fault_clear_w1c_o(cfg_fault_clear_w1c),
    .irq_enable_o(irq_enable),
    .status_fault_sticky_i(fault_sticky),
    .status_response_ready_i(response_ready_pulse),
    .status_fresh_i(fresh),
    .status_stale_i(stale),
    .status_timeout_i(timeout),
    .status_last_seen_sequence_i(last_seen_sequence),
    .status_actuator_cmd_i(actuator_cmd_int),
    .status_irq_summary_i(irq_status_int)
);

adaptive_aero_control_request_formatter u_req (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable_i(cfg_enable),
    .cfg_arm_i(cfg_arm),
    .cfg_mode_i(cfg_mode),
    .cfg_velocity_setpoint_i(cfg_velocity_setpoint),
    .cfg_sequence_counter_i(cfg_sequence_counter),
    .req_due_i(cfg_arm),
    .local_timestamp_i(cfg_velocity_setpoint),
    .request_id_i(cfg_sequence_counter),
    .stream_req_ready_i(stream_req_ready_i),
    .stream_req_valid_o(stream_req_valid_int),
    .stream_req_data_o(stream_req_data_int),
    .request_issued_o(),
    .request_sequence_o()
);

adaptive_aero_control_response_parser u_rsp (
    .clk(clk),
    .reset_n(reset_n),
    .stream_rsp_valid_i(stream_rsp_valid_i),
    .stream_rsp_ready_o(stream_rsp_ready_int),
    .stream_rsp_data_i(stream_rsp_data_i),
    .response_valid_o(response_valid),
    .response_id_o(),
    .response_sequence_o(response_sequence),
    .response_fresh_o(response_fresh),
    .response_drag_o(response_drag),
    .response_lift_o(response_lift),
    .response_status_flags_o(response_status_flags),
    .response_ready_pulse_o(response_ready_pulse)
);

adaptive_aero_control_safety_supervisor u_safety (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable_i(cfg_enable),
    .cfg_arm_i(cfg_arm),
    .cfg_timeout_threshold_i(cfg_timeout_threshold),
    .cfg_sequence_counter_i(cfg_sequence_counter),
    .cfg_fault_clear_w1c_i(cfg_fault_clear_w1c),
    .response_valid_i(response_valid),
    .response_sequence_i(response_sequence),
    .response_fresh_i(response_fresh),
    .response_status_flags_i(response_status_flags),
    .local_timestamp_i(cfg_velocity_setpoint),
    .last_seen_sequence_o(last_seen_sequence),
    .fresh_o(fresh),
    .stale_o(stale),
    .timeout_o(timeout),
    .fault_sticky_o(fault_sticky),
    .irq_event_o(),
    .allow_command_o(allow_command)
);

adaptive_aero_control_command_clamper u_clamp (
    .clk(clk),
    .reset_n(reset_n),
    .command_enable_i(allow_command),
    .response_valid_i(response_valid),
    .response_drag_i(response_drag),
    .response_lift_i(response_lift),
    .cfg_clamp_min_i(cfg_clamp_min),
    .cfg_clamp_max_i(cfg_clamp_max),
    .actuator_cmd_o(actuator_cmd_int),
    .actuator_cmd_valid_o(),
    .command_clamped_o()
);

adaptive_aero_control_interrupt_gen u_irq (
    .clk(clk),
    .reset_n(reset_n),
    .irq_enable_i(irq_enable),
    .response_ready_pulse_i(response_ready_pulse),
    .stale_i(stale),
    .timeout_i(timeout),
    .fault_sticky_i(fault_sticky),
    .irq_o(irq_int),
    .irq_status_o(irq_status_int)
);

assign wb_dat_o = wb_dat_int;
assign wb_ack_o = wb_ack_int;
assign wb_err_o = wb_err_int;
assign stream_req_valid_o = stream_req_valid_int;
assign stream_req_data_o = stream_req_data_int;
assign stream_rsp_ready_o = stream_rsp_ready_int;
assign actuator_cmd_o = actuator_cmd_int;
assign irq_o = irq_int;
assign uart_tx_o = wb_err_int;
endmodule
