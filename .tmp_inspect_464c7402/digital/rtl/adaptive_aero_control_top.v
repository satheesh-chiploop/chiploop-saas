module adaptive_aero_control_top (
    clk,
    rst_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_sel_i,
    wb_ack_o,
    wb_err_o,
    req_stream_data,
    req_stream_valid,
    req_stream_ready,
    rsp_stream_data,
    rsp_stream_valid,
    rsp_stream_ready,
    actuator_cmd,
    actuator_cmd_valid,
    fault_status,
    uart_tx,
    uart_rx
);

input clk;
input rst_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input wb_cyc_i;
input wb_stb_i;
input wb_we_i;
input [3:0] wb_sel_i;
output wb_ack_o;
output wb_err_o;
output [127:0] req_stream_data;
output req_stream_valid;
input req_stream_ready;
input [127:0] rsp_stream_data;
input rsp_stream_valid;
output rsp_stream_ready;
output [15:0] actuator_cmd;
output actuator_cmd_valid;
output [7:0] fault_status;
output uart_tx;
input uart_rx;
wire ctrl_enable;
wire ctrl_clear_fault;
wire ctrl_arm_output;
wire ctrl_request_start;
wire ctrl_bypass_model;
wire status_busy;
wire status_req_pending;
wire status_rsp_seen;
wire status_stale_fault;
wire status_timeout_fault;
wire status_range_fault;
wire status_fallback_active;
wire status_last_good_valid;
wire [31:0] timeout_cfg_cycles;
wire [31:0] stale_cfg_cycles;
wire [15:0] cmd_min;
wire [15:0] cmd_max;
wire [15:0] cmd_safe;
wire [15:0] seq_tx;
wire [15:0] seq_rx;
wire [7:0] meta_velocity_bucket;
wire [3:0] meta_mode;
wire [3:0] meta_env_flags;
wire [15:0] meta_session_id;
wire [15:0] rsp_seq_rx;
wire [7:0] rsp_status;
wire [15:0] rsp_cmd_suggest;
wire [7:0] rsp_quality;
wire [15:0] rsp_age_echo;
wire req_pending;
wire rsp_seen;

assign uart_tx = uart_rx;

adaptive_aero_control_csr_mmio u_csr_mmio (
    .clk(clk),
    .rst_n(rst_n),
    .wb_adr_i(wb_adr_i),
    .wb_dat_i(wb_dat_i),
    .wb_dat_o(wb_dat_o),
    .wb_cyc_i(wb_cyc_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .wb_sel_i(wb_sel_i),
    .wb_ack_o(wb_ack_o),
    .wb_err_o(wb_err_o),
    .ctrl_enable(ctrl_enable),
    .ctrl_clear_fault(ctrl_clear_fault),
    .ctrl_arm_output(ctrl_arm_output),
    .ctrl_request_start(ctrl_request_start),
    .ctrl_bypass_model(ctrl_bypass_model),
    .status_busy(status_busy),
    .status_req_pending(status_req_pending),
    .status_rsp_seen(status_rsp_seen),
    .status_stale_fault(status_stale_fault),
    .status_timeout_fault(status_timeout_fault),
    .status_range_fault(status_range_fault),
    .status_fallback_active(status_fallback_active),
    .status_last_good_valid(status_last_good_valid),
    .timeout_cfg_cycles(timeout_cfg_cycles),
    .stale_cfg_cycles(stale_cfg_cycles),
    .cmd_min(cmd_min),
    .cmd_max(cmd_max),
    .cmd_safe(cmd_safe),
    .seq_tx(seq_tx),
    .seq_rx(seq_rx),
    .meta_velocity_bucket(meta_velocity_bucket),
    .meta_mode(meta_mode),
    .meta_env_flags(meta_env_flags),
    .meta_session_id(meta_session_id)
);

adaptive_aero_control_packet_io u_packet_io (
    .clk(clk),
    .rst_n(rst_n),
    .ctrl_enable(ctrl_enable),
    .ctrl_arm_output(ctrl_arm_output),
    .ctrl_request_start(ctrl_request_start),
    .ctrl_bypass_model(ctrl_bypass_model),
    .seq_tx(seq_tx),
    .timeout_cfg_cycles(timeout_cfg_cycles),
    .stale_cfg_cycles(stale_cfg_cycles),
    .meta_velocity_bucket(meta_velocity_bucket),
    .meta_mode(meta_mode),
    .meta_env_flags(meta_env_flags),
    .meta_session_id(meta_session_id),
    .req_stream_data(req_stream_data),
    .req_stream_valid(req_stream_valid),
    .req_stream_ready(req_stream_ready),
    .rsp_stream_data(rsp_stream_data),
    .rsp_stream_valid(rsp_stream_valid),
    .rsp_stream_ready(rsp_stream_ready),
    .rsp_seq_rx(rsp_seq_rx),
    .rsp_status(rsp_status),
    .rsp_cmd_suggest(rsp_cmd_suggest),
    .rsp_quality(rsp_quality),
    .rsp_age_echo(rsp_age_echo),
    .req_pending(req_pending),
    .rsp_seen(rsp_seen)
);

adaptive_aero_control_supervisor u_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .ctrl_enable(ctrl_enable),
    .ctrl_clear_fault(ctrl_clear_fault),
    .ctrl_arm_output(ctrl_arm_output),
    .ctrl_bypass_model(ctrl_bypass_model),
    .timeout_cfg_cycles(timeout_cfg_cycles),
    .stale_cfg_cycles(stale_cfg_cycles),
    .cmd_min(cmd_min),
    .cmd_max(cmd_max),
    .cmd_safe(cmd_safe),
    .seq_tx(seq_tx),
    .seq_rx(seq_rx),
    .rsp_seq_rx(rsp_seq_rx),
    .rsp_status(rsp_status),
    .rsp_cmd_suggest(rsp_cmd_suggest),
    .rsp_quality(rsp_quality),
    .rsp_age_echo(rsp_age_echo),
    .meta_velocity_bucket(meta_velocity_bucket),
    .meta_mode(meta_mode),
    .meta_env_flags(meta_env_flags),
    .meta_session_id(meta_session_id),
    .status_busy(status_busy),
    .status_req_pending(status_req_pending),
    .status_rsp_seen(status_rsp_seen),
    .status_stale_fault(status_stale_fault),
    .status_timeout_fault(status_timeout_fault),
    .status_range_fault(status_range_fault),
    .status_fallback_active(status_fallback_active),
    .status_last_good_valid(status_last_good_valid),
    .actuator_cmd(actuator_cmd),
    .actuator_cmd_valid(actuator_cmd_valid),
    .fault_status(fault_status)
);

endmodule
