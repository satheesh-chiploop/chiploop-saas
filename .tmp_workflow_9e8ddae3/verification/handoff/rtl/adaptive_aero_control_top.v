module adaptive_aero_control_top (
    input clk,
    input reset_n,
    input [7:0] mmio_addr,
    input [31:0] mmio_wdata,
    input mmio_valid,
    input mmio_write,
    output [31:0] mmio_rdata,
    output mmio_ready,
    output req_valid,
    input req_ready,
    output [127:0] req_data,
    input resp_valid,
    output resp_ready,
    input [127:0] resp_data,
    output actuator_valid,
    output [15:0] actuator_cmd,
    output safe_fallback_active,
    input [15:0] response_seq_probe,
    input [7:0] response_status_flags_probe,
    output timeout_expired,
    output [15:0] current_cycle_age,
    output bram_csb,
    output bram_web,
    output [8:0] bram_addr,
    output [31:0] bram_din
);
wire cfg_enable;
wire [2:0] cfg_mode_select;
wire [15:0] cfg_timeout_limit;
wire [15:0] cfg_stale_age_limit;
wire [15:0] cfg_actuator_min;
wire [15:0] cfg_actuator_max;
wire [15:0] cfg_rate_limit;
wire [15:0] cfg_sequence_seed;
wire cfg_status_clear;
wire cfg_pipelined_mode;
wire [15:0] cfg_safe_fallback_cmd;
wire [15:0] cfg_nominal_stream_velocity;
wire [15:0] cfg_geometry_descriptor_id;
wire [7:0] status_code;
wire [7:0] fault_flags;
wire [15:0] request_counter;
wire [15:0] response_counter;
wire [7:0] current_state;
wire [15:0] debug_counter0;
wire [15:0] debug_counter1;
wire req_issued;
wire [15:0] request_seq;
wire [15:0] request_timestamp;
wire request_context_valid;
wire response_accepted;
wire response_rejected;
wire [15:0] response_seq;
wire [15:0] response_suggestion;
wire [7:0] response_status_flags;
wire response_validity_ok;
wire response_fresh_ok;
wire fault_timeout;
wire fault_stale;
wire fault_sequence_mismatch;
wire fault_invalid_packet;
wire fault_transport_error;
wire command_clamp_active;
wire fallback_active_latched;
wire request_busy;
wire [31:0] bram_dout_unused;
wire [15:0] age_calc;
assign current_cycle_age = age_calc;
assign timeout_expired = (cfg_timeout_limit != 16'h0000) && (age_calc >= cfg_timeout_limit);

assign bram_csb = 1'b1;
assign bram_web = 1'b1;
assign bram_addr = 9'h000;
assign bram_din = 32'h00000000;

assign age_calc = request_context_valid ? (request_counter - request_timestamp) : 16'h0000;

adaptive_aero_control_csr_mmio u_csr (
    .clk(clk),
    .reset_n(reset_n),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_valid(mmio_valid),
    .mmio_write(mmio_write),
    .mmio_rdata(mmio_rdata),
    .mmio_ready(mmio_ready),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_stale_age_limit(cfg_stale_age_limit),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_rate_limit(cfg_rate_limit),
    .cfg_sequence_seed(cfg_sequence_seed),
    .cfg_status_clear(cfg_status_clear),
    .cfg_pipelined_mode(cfg_pipelined_mode),
    .cfg_safe_fallback_cmd(cfg_safe_fallback_cmd),
    .cfg_nominal_stream_velocity(cfg_nominal_stream_velocity),
    .cfg_geometry_descriptor_id(cfg_geometry_descriptor_id),
    .status_code(status_code),
    .fault_flags(fault_flags),
    .request_counter(request_counter),
    .response_counter(response_counter),
    .current_state(current_state),
    .debug_counter0(debug_counter0),
    .debug_counter1(debug_counter1)
);

adaptive_aero_request_engine u_req (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_mode_select(cfg_mode_select),
    .cfg_pipelined_mode(cfg_pipelined_mode),
    .cfg_nominal_stream_velocity(cfg_nominal_stream_velocity),
    .cfg_geometry_descriptor_id(cfg_geometry_descriptor_id),
    .seq_seed(cfg_sequence_seed),
    .req_ready(req_ready),
    .req_valid(req_valid),
    .req_data(req_data),
    .req_issued(req_issued),
    .request_seq(request_seq),
    .request_busy(request_busy),
    .request_timestamp(request_timestamp),
    .request_context_valid(request_context_valid)
);

adaptive_aero_response_validator u_val (
    .clk(clk),
    .reset_n(reset_n),
    .resp_valid(resp_valid),
    .resp_data(resp_data),
    .resp_ready(resp_ready),
    .request_seq(request_seq),
    .request_timestamp(request_timestamp),
    .request_context_valid(request_context_valid),
    .cfg_timeout_limit(cfg_timeout_limit),
    .cfg_stale_age_limit(cfg_stale_age_limit),
    .cfg_enable(cfg_enable),
    .timeout_expired(timeout_expired),
    .current_cycle_age(current_cycle_age),
    .response_accepted(response_accepted),
    .response_rejected(response_rejected),
    .response_seq(response_seq),
    .response_suggestion(response_suggestion),
    .response_status_flags(response_status_flags),
    .response_validity_ok(response_validity_ok),
    .response_fresh_ok(response_fresh_ok),
    .fault_timeout(fault_timeout),
    .fault_stale(fault_stale),
    .fault_sequence_mismatch(fault_sequence_mismatch),
    .fault_invalid_packet(fault_invalid_packet),
    .fault_transport_error(fault_transport_error)
);

adaptive_aero_command_safety u_cmd (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_actuator_min(cfg_actuator_min),
    .cfg_actuator_max(cfg_actuator_max),
    .cfg_rate_limit(cfg_rate_limit),
    .cfg_safe_fallback_cmd(cfg_safe_fallback_cmd),
    .response_accepted(response_accepted),
    .response_suggestion(response_suggestion),
    .response_validity_ok(response_validity_ok),
    .response_fresh_ok(response_fresh_ok),
    .fault_timeout(fault_timeout),
    .fault_stale(fault_stale),
    .fault_sequence_mismatch(fault_sequence_mismatch),
    .fault_invalid_packet(fault_invalid_packet),
    .fault_transport_error(fault_transport_error),
    .actuator_valid(actuator_valid),
    .actuator_cmd(actuator_cmd),
    .safe_fallback_active(safe_fallback_active),
    .command_clamp_active(command_clamp_active),
    .fallback_active_latched(fallback_active_latched)
);

adaptive_aero_status_telemetry u_tel (
    .clk(clk),
    .reset_n(reset_n),
    .response_accepted(response_accepted),
    .request_issued(req_issued),
    .fallback_active_latched(fallback_active_latched),
    .command_clamp_active(command_clamp_active),
    .fault_timeout(fault_timeout),
    .fault_stale(fault_stale),
    .fault_sequence_mismatch(fault_sequence_mismatch),
    .fault_invalid_packet(fault_invalid_packet),
    .fault_transport_error(fault_transport_error),
    .status_clear(cfg_status_clear),
    .current_state(current_state),
    .status_code(status_code),
    .fault_flags(fault_flags),
    .request_counter(request_counter),
    .response_counter(response_counter),
    .debug_counter0(debug_counter0),
    .debug_counter1(debug_counter1)
);

fpga_bram_512x32 u_bram (
    .clk(clk),
    .csb(bram_csb),
    .web(bram_web),
    .addr(bram_addr),
    .din(bram_din),
    .dout(bram_dout_unused)
);

endmodule
