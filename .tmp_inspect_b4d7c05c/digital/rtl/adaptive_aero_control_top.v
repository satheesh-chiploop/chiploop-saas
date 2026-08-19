module adaptive_aero_control_top (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_sel_i,
    wb_ack_o,
    wb_err_o,
    aero_req_valid,
    aero_req_ready,
    aero_req_payload,
    aero_rsp_valid,
    aero_rsp_ready,
    aero_rsp_payload,
    actuator_valid,
    actuator_command,
    interrupt_o
);
    input clk;
    input reset_n;
    input [31:0] wb_adr_i;
    input [31:0] wb_dat_i;
    output [31:0] wb_dat_o;
    input wb_cyc_i;
    input wb_stb_i;
    input wb_we_i;
    input [3:0] wb_sel_i;
    output wb_ack_o;
    output wb_err_o;
    output aero_req_valid;
    input aero_req_ready;
    output [127:0] aero_req_payload;
    input aero_rsp_valid;
    output aero_rsp_ready;
    input [127:0] aero_rsp_payload;
    output actuator_valid;
    output [31:0] actuator_command;
    output interrupt_o;
wire start_request;
wire clear_faults;
wire safe_mode_select;
wire [15:0] request_seq;
wire [31:0] stream_velocity;
wire [15:0] geometry_id;
wire [3:0] flow_condition_sel;
wire [3:0] control_mode;
wire [31:0] timeout_cycles;
wire [31:0] freshness_cycles;
wire [31:0] actuator_min;
wire [31:0] actuator_max;
wire [31:0] rate_limit;
wire config_valid;
wire busy;
wire response_valid;
    wire timeout_fault;
wire stale_fault;
wire response_seq_mismatch;
wire invalid_payload_fault;
wire fallback_active;
wire [31:0] last_good_command;
wire [15:0] current_sequence;
wire fault_pending;
wire request_issued;
wire request_invalid;
wire [127:0] req_payload;
wire req_valid;
    wire req_ready;
wire request_manager_busy;
    wire rsp_ready;
wire [15:0] response_seq;
wire [31:0] drag_estimate;
wire [31:0] lift_estimate;
wire [7:0] confidence_flags;
    wire [7:0] diagnostic_code;
    wire response_valid_int;
    wire response_seq_mismatch_int;
    wire stale_fault_int;
    wire invalid_payload_fault_int;
wire freshness_ok;
    wire watchdog_active;
wire timeout_expired;
wire allow_command_update;
wire actuator_enable;
wire fault_latched;
wire response_accepted;
wire [15:0] expected_seq;
    wishbone_csr_mmio u_wishbone_csr_mmio (
        .clk(clk),
        .reset_n(reset_n),
        .wb_adr_i(wb_adr_i),
        .wb_dat_i(wb_dat_i),
        .wb_dat_o(wb_dat_o),
        .wb_cyc_i(wb_cyc_i),
        .wb_stb_i(wb_stb_i),
        .wb_we_i(wb_we_i),
        .wb_sel_i(wb_sel_i),
        .wb_ack_o(wb_ack_o),
        .wb_err_o(wb_err_o),
        .start_request(start_request),
        .clear_faults(clear_faults),
        .safe_mode_select(safe_mode_select),
        .request_seq(request_seq),
        .stream_velocity(stream_velocity),
        .geometry_id(geometry_id),
        .flow_condition_sel(flow_condition_sel),
        .control_mode(control_mode),
        .timeout_cycles(timeout_cycles),
        .freshness_cycles(freshness_cycles),
        .actuator_min(actuator_min),
        .actuator_max(actuator_max),
        .rate_limit(rate_limit),
        .config_valid(config_valid),
        .busy(busy),
        .response_valid(response_valid),
        .timeout_fault(timeout_fault),
        .stale_fault(stale_fault),
        .response_seq_mismatch(response_seq_mismatch),
        .invalid_payload_fault(invalid_payload_fault),
        .fallback_active(fallback_active),
        .last_good_command(last_good_command),
        .current_sequence(current_sequence),
        .fault_pending(fault_pending),
        .interrupt_o(interrupt_o)
    );

    request_manager u_request_manager (
        .clk(clk),
        .reset_n(reset_n),
        .start_request(start_request),
        .clear_faults(clear_faults),
        .request_seq(request_seq),
        .stream_velocity(stream_velocity),
        .geometry_id(geometry_id),
        .flow_condition_sel(flow_condition_sel),
        .control_mode(control_mode),
        .config_valid(config_valid),
        .busy(busy),
        .req_payload(req_payload),
        .req_valid(req_valid),
        .req_ready(aero_req_ready),
        .req_issued(request_issued),
        .request_seq_latched(),
        .request_invalid(request_invalid),
        .timeout_expired(timeout_expired),
        .fault_latched(fault_latched)
    );

    response_adapter u_response_adapter (
        .clk(clk),
        .reset_n(reset_n),
        .rsp_valid(aero_rsp_valid),
        .rsp_ready(rsp_ready),
        .rsp_payload(aero_rsp_payload),
        .busy(request_manager_busy),
        .expected_seq(current_sequence),
        .freshness_ok(freshness_ok),
        .timeout_expired(timeout_expired),
        .response_seq(response_seq),
        .drag_estimate(drag_estimate),
        .lift_estimate(lift_estimate),
        .confidence_flags(confidence_flags),
        .diagnostic_code(diagnostic_code),
        .response_valid(response_valid_int),
        .response_seq_mismatch(response_seq_mismatch_int),
        .stale_fault(stale_fault_int),
        .invalid_payload_fault(invalid_payload_fault_int)
    );

    timeout_watchdog u_timeout_watchdog (
        .clk(clk),
        .reset_n(reset_n),
        .request_issued(request_issued),
        .response_accepted(response_valid_int),
        .clear_faults(clear_faults),
        .timeout_cycles(timeout_cycles),
        .freshness_cycles(freshness_cycles),
        .busy(busy),
        .timeout_expired(timeout_expired),
        .freshness_ok(freshness_ok),
        .watchdog_active(watchdog_active)
    );

    safety_supervisor u_safety_supervisor (
        .clk(clk),
        .reset_n(reset_n),
        .config_valid(config_valid),
        .request_invalid(request_invalid),
        .response_valid(response_valid_int),
        .response_seq_mismatch(response_seq_mismatch_int),
        .stale_fault(stale_fault_int),
        .invalid_payload_fault(invalid_payload_fault_int),
        .timeout_expired(timeout_expired),
        .safe_mode_select(safe_mode_select),
        .clear_faults(clear_faults),
        .busy(busy),
        .response_seq(response_seq),
        .current_sequence(current_sequence),
        .fault_pending(fault_pending),
        .allow_command_update(allow_command_update),
        .actuator_enable(actuator_enable),
        .fault_latched(fault_latched)
    );

    actuator_command_unit u_actuator_command_unit (
        .clk(clk),
        .reset_n(reset_n),
        .actuator_enable(actuator_enable),
        .allow_command_update(allow_command_update),
        .drag_estimate(drag_estimate),
        .lift_estimate(lift_estimate),
        .confidence_flags(confidence_flags),
        .actuator_min(actuator_min),
        .actuator_max(actuator_max),
        .rate_limit(rate_limit),
        .safe_mode_select(safe_mode_select),
        .actuator_valid(actuator_valid),
        .actuator_command(actuator_command),
        .last_good_command(last_good_command)
    );

    assign aero_req_valid = req_valid;
    assign aero_req_payload = req_payload;
    assign aero_rsp_ready = rsp_ready;
    assign request_manager_busy = busy;

assign response_valid = response_valid_int;
assign response_seq_mismatch = response_seq_mismatch_int;
assign stale_fault = stale_fault_int;
assign invalid_payload_fault = invalid_payload_fault_int;
assign timeout_fault = timeout_expired;
assign fallback_active = fault_pending;

endmodule
