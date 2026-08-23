module adaptive_aero_control_top (
    input clk,
    input rst_n,
    input reg_valid,
    input reg_we,
    input reg_re,
    input [7:0] reg_addr,
    input [31:0] reg_wdata,
    input [3:0] reg_byte_en,
    output reg_ready,
    output [31:0] reg_rdata,
    input req_valid,
    input [127:0] req_data,
    output req_ready,
    input rsp_valid,
    input [127:0] rsp_data,
    output rsp_ready,
    output act_cmd_valid,
    output [15:0] act_cmd,
    output act_cmd_hold,
    output act_fault
);
wire cfg_enable;
wire [1:0] cfg_mode_sel;
wire [15:0] cfg_env_limit;
wire [15:0] cfg_stale_timeout;
wire [15:0] cfg_seq_base;
wire [15:0] cfg_heartbeat_timeout;
wire [15:0] cfg_act_min;
wire [15:0] cfg_act_max;
wire [7:0] cfg_rate_limit;
wire [15:0] cfg_safe_output;
wire cfg_fault_clear;
wire cfg_reserved_error_en;
wire fault_latched_clear;
wire [1:0] status_mode;
wire status_fault_latched;
wire status_timeout;
wire status_stale;
wire status_heartbeat_seen;
wire [15:0] status_last_cmd;
wire [15:0] status_last_seq;
wire [15:0] telemetry_accepted_packets;
wire [15:0] telemetry_rejected_packets;
wire [15:0] telemetry_timeout_events;
wire [15:0] telemetry_stale_events;
wire [15:0] telemetry_fallback_entries;
wire [15:0] telemetry_last_valid_seq;
wire rx_pkt_valid;
wire [15:0] rx_pkt_seq;
wire [15:0] rx_pkt_timestamp;
wire [3:0] rx_pkt_cmd_type;
wire [7:0] rx_pkt_vel_bin;
wire [15:0] rx_pkt_geom_ref;
wire [7:0] rx_pkt_integrity;
wire [15:0] rx_pkt_age;
wire req_accept;
wire req_reject;
wire req_fault;
wire req_stale;
wire req_timeout;
wire req_seq_ok;
wire req_integrity_ok;
wire req_env_ok;
wire rsp_accept;
wire rsp_reject;
wire rsp_seq_ok;
wire rsp_fresh_ok;
wire rsp_cmd_valid;
wire [15:0] rsp_act_cmd;
wire heartbeat_seen;
wire [15:0] last_valid_seq;
wire fallback_entry;
wire safety_supervisor_active;
wire safety_supervisor_wait_response;
wire [1:0] status_mode_seen;
wire [127:0] bram_dout;
wire bram_csb;
wire bram_we;
wire [3:0] bram_addr;
wire [127:0] bram_din;
wire [31:0] bram_read_word;

wire [31:0] reg_rdata_int;
fpga_bram_buffer u_fpga_bram_buffer (
    .clk(clk),
    .csb(bram_csb),
    .we(bram_we),
    .addr(bram_addr),
    .din(bram_din),
    .dout(bram_dout)
);

host_reg_window u_host_reg_window (
    .clk(clk),
    .rst_n(rst_n),
    .reg_valid(reg_valid),
    .reg_we(reg_we),
    .reg_re(reg_re),
    .reg_addr(reg_addr),
    .reg_wdata(reg_wdata),
    .reg_byte_en(reg_byte_en),
    .reg_ready(reg_ready),
    .reg_rdata(reg_rdata_int),
    .cfg_enable(cfg_enable),
    .cfg_mode_sel(cfg_mode_sel),
    .cfg_env_limit(cfg_env_limit),
    .cfg_stale_timeout(cfg_stale_timeout),
    .cfg_seq_base(cfg_seq_base),
    .cfg_heartbeat_timeout(cfg_heartbeat_timeout),
    .cfg_act_min(cfg_act_min),
    .cfg_act_max(cfg_act_max),
    .cfg_rate_limit(cfg_rate_limit),
    .cfg_safe_output(cfg_safe_output),
    .cfg_fault_clear(cfg_fault_clear),
    .cfg_reserved_error_en(cfg_reserved_error_en),
    .status_mode(status_mode),
    .status_fault_latched(status_fault_latched),
    .status_timeout(status_timeout),
    .status_stale(status_stale),
    .status_heartbeat_seen(status_heartbeat_seen),
    .status_last_cmd(status_last_cmd),
    .status_last_seq(status_last_seq),
    .telemetry_accepted_packets(telemetry_accepted_packets),
    .telemetry_rejected_packets(telemetry_rejected_packets),
    .telemetry_timeout_events(telemetry_timeout_events),
    .telemetry_stale_events(telemetry_stale_events),
    .telemetry_fallback_entries(telemetry_fallback_entries),
    .telemetry_last_valid_seq(telemetry_last_valid_seq),
    .fault_latched_clear(fault_latched_clear)
);

stream_rx u_stream_rx (
    .clk(clk),
    .rst_n(rst_n),
    .req_valid(req_valid),
    .req_data(req_data),
    .req_ready(req_ready),
    .rx_pkt_valid(rx_pkt_valid),
    .rx_pkt_seq(rx_pkt_seq),
    .rx_pkt_timestamp(rx_pkt_timestamp),
    .rx_pkt_cmd_type(rx_pkt_cmd_type),
    .rx_pkt_vel_bin(rx_pkt_vel_bin),
    .rx_pkt_geom_ref(rx_pkt_geom_ref),
    .rx_pkt_integrity(rx_pkt_integrity),
    .rx_pkt_age(rx_pkt_age)
);

request_validator u_request_validator (
    .clk(clk),
    .rst_n(rst_n),
    .rx_pkt_valid(rx_pkt_valid),
    .rx_pkt_seq(rx_pkt_seq),
    .rx_pkt_timestamp(rx_pkt_timestamp),
    .rx_pkt_cmd_type(rx_pkt_cmd_type),
    .rx_pkt_vel_bin(rx_pkt_vel_bin),
    .rx_pkt_geom_ref(rx_pkt_geom_ref),
    .rx_pkt_integrity(rx_pkt_integrity),
    .rx_pkt_age(rx_pkt_age),
    .rsp_valid(rsp_valid),
    .rsp_data(rsp_data),
    .rsp_ready(rsp_ready),
    .cfg_enable(cfg_enable),
    .cfg_mode_sel(cfg_mode_sel),
    .cfg_env_limit(cfg_env_limit),
    .cfg_stale_timeout(cfg_stale_timeout),
    .cfg_seq_base(cfg_seq_base),
    .cfg_heartbeat_timeout(cfg_heartbeat_timeout),
    .req_accept(req_accept),
    .req_reject(req_reject),
    .req_fault(req_fault),
    .req_stale(req_stale),
    .req_timeout(req_timeout),
    .req_seq_ok(req_seq_ok),
    .req_integrity_ok(req_integrity_ok),
    .req_env_ok(req_env_ok),
    .rsp_accept(rsp_accept),
    .rsp_reject(rsp_reject),
    .rsp_seq_ok(rsp_seq_ok),
    .rsp_fresh_ok(rsp_fresh_ok),
    .rsp_cmd_valid(rsp_cmd_valid),
    .rsp_act_cmd(rsp_act_cmd),
    .heartbeat_seen(heartbeat_seen),
    .last_valid_seq(last_valid_seq)
);

safety_supervisor u_safety_supervisor (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_enable(cfg_enable),
    .cfg_mode_sel(cfg_mode_sel),
    .cfg_fault_clear(cfg_fault_clear),
    .fault_latched_clear(fault_latched_clear),
    .req_accept(req_accept),
    .req_reject(req_reject),
    .req_fault(req_fault),
    .req_stale(req_stale),
    .req_timeout(req_timeout),
    .rsp_accept(rsp_accept),
    .rsp_reject(rsp_reject),
    .rsp_fresh_ok(rsp_fresh_ok),
    .heartbeat_seen(heartbeat_seen),
    .status_mode(status_mode),
    .fault_latched(act_fault),
    .timeout_status(status_timeout),
    .stale_status(status_stale),
    .fallback_entry(fallback_entry),
    .armed(),
    .active(safety_supervisor_active),
    .wait_response(safety_supervisor_wait_response)
);

command_conditioner u_command_conditioner (
    .clk(clk),
    .rst_n(rst_n),
    .status_mode(status_mode),
    .fault_latched(act_fault),
    .timeout_status(status_timeout),
    .stale_status(status_stale),
    .active(safety_supervisor_active),
    .wait_response(safety_supervisor_wait_response),
    .rsp_cmd_valid(rsp_cmd_valid),
    .rsp_act_cmd(rsp_act_cmd),
    .cfg_act_min(cfg_act_min),
    .cfg_act_max(cfg_act_max),
    .cfg_rate_limit(cfg_rate_limit),
    .cfg_safe_output(cfg_safe_output),
    .status_mode_seen(status_mode_seen),
    .act_cmd_valid(act_cmd_valid),
    .act_cmd(act_cmd),
    .act_cmd_hold(act_cmd_hold),
    .last_cmd(status_last_cmd)
);

telemetry_logger u_telemetry_logger (
    .clk(clk),
    .rst_n(rst_n),
    .req_accept(req_accept),
    .req_reject(req_reject),
    .req_timeout(req_timeout),
    .req_stale(req_stale),
    .fallback_entry(fallback_entry),
    .last_valid_seq(last_valid_seq),
    .telemetry_accepted_packets(telemetry_accepted_packets),
    .telemetry_rejected_packets(telemetry_rejected_packets),
    .telemetry_timeout_events(telemetry_timeout_events),
    .telemetry_stale_events(telemetry_stale_events),
    .telemetry_fallback_entries(telemetry_fallback_entries),
    .telemetry_last_valid_seq(telemetry_last_valid_seq)
);

assign reg_rdata = reg_rdata_int;
assign bram_csb = ~(reg_valid && (reg_addr[7:4] == 4'h8));
assign bram_we = reg_we;
assign bram_addr = reg_addr[3:0];
assign bram_din = {96'h000000000000000000000000, reg_wdata};
assign bram_read_word = bram_dout[31:0];

assign status_fault_latched = act_fault;
assign status_heartbeat_seen = heartbeat_seen;
assign status_last_seq = last_valid_seq;

endmodule
