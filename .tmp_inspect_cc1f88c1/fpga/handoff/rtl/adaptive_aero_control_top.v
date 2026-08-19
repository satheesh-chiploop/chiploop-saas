module adaptive_aero_control_top (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_we_i,
    wb_cyc_i,
    wb_stb_i,
    wb_ack_o,
    wb_stall_o,
    wb_err_o,
    wb_sel_i,
    wb_cti_i,
    wb_bte_i,
    irq_o,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    actuator_cmd_valid,
    actuator_cmd_ready,
    actuator_cmd_data
);
    input clk;
    input reset_n;
    input [31:0] wb_adr_i;
    input [31:0] wb_dat_i;
    output [31:0] wb_dat_o;
    input wb_we_i;
    input wb_cyc_i;
    input wb_stb_i;
    output wb_ack_o;
    output wb_stall_o;
    output wb_err_o;
    input [3:0] wb_sel_i;
    input [2:0] wb_cti_i;
    input [1:0] wb_bte_i;
    output irq_o;
    output model_req_valid;
    output [63:0] model_req_data;
    input model_req_ready;
    input model_rsp_valid;
    input [63:0] model_rsp_data;
    output model_rsp_ready;
    output actuator_cmd_valid;
    input actuator_cmd_ready;
    output [31:0] actuator_cmd_data;
wire cfg_global_enable;
wire cfg_release_enable;
wire cfg_clear_faults;
wire cfg_request_launch;
wire [1:0] cfg_mode_sel;
wire [15:0] cfg_timeout_threshold;
wire [15:0] cfg_stale_age_threshold;
wire [15:0] cfg_actuator_min_limit;
wire [15:0] cfg_actuator_max_limit;
wire [15:0] cfg_actuator_rate_limit;
wire [31:0] cfg_request_payload;
    wire cfg_interrupt_ack;
    wire status_busy;
    wire status_response_ready;
    wire status_stale_rejected;
    wire status_timeout_fault;
    wire status_invalid_response;
    wire status_clamp_applied;
    wire status_fallback_active;
    wire status_sequence_mismatch;
wire [15:0] current_sequence_id;
wire [31:0] last_accepted_command;
    wire [63:0] last_response_summary;
wire [15:0] sticky_faults;
    wire irq_pending;
wire busy;
wire response_ready;
wire stale_rejected;
wire timeout_fault;
wire invalid_response;
wire sequence_mismatch;
wire [63:0] accepted_response_summary;
    wire [15:0] request_timestamp;
wire fault_event_pulse;
wire clamp_applied;
wire fallback_active;
    assign irq_o = irq_pending | response_ready | timeout_fault | stale_rejected | invalid_response | sequence_mismatch;

    adaptive_aero_control_mmio u_mmio (
        .clk(clk),
        .reset_n(reset_n),
        .wb_adr_i(wb_adr_i),
        .wb_dat_i(wb_dat_i),
        .wb_dat_o(wb_dat_o),
        .wb_we_i(wb_we_i),
        .wb_cyc_i(wb_cyc_i),
        .wb_stb_i(wb_stb_i),
        .wb_ack_o(wb_ack_o),
        .wb_stall_o(wb_stall_o),
        .wb_err_o(wb_err_o),
        .wb_sel_i(wb_sel_i),
        .wb_cti_i(wb_cti_i),
        .wb_bte_i(wb_bte_i),
        .cfg_global_enable(cfg_global_enable),
        .cfg_release_enable(cfg_release_enable),
        .cfg_clear_faults(cfg_clear_faults),
        .cfg_request_launch(cfg_request_launch),
        .cfg_mode_sel(cfg_mode_sel),
        .cfg_timeout_threshold(cfg_timeout_threshold),
        .cfg_stale_age_threshold(cfg_stale_age_threshold),
        .cfg_actuator_min_limit(cfg_actuator_min_limit),
        .cfg_actuator_max_limit(cfg_actuator_max_limit),
        .cfg_actuator_rate_limit(cfg_actuator_rate_limit),
        .cfg_request_payload(cfg_request_payload),
        .cfg_interrupt_ack(cfg_interrupt_ack),
        .status_busy(status_busy),
        .status_response_ready(status_response_ready),
        .status_stale_rejected(status_stale_rejected),
        .status_timeout_fault(status_timeout_fault),
        .status_invalid_response(status_invalid_response),
        .status_clamp_applied(status_clamp_applied),
        .status_fallback_active(status_fallback_active),
        .status_sequence_mismatch(status_sequence_mismatch),
        .current_sequence_id(current_sequence_id),
        .last_accepted_command(last_accepted_command),
        .last_response_summary(last_response_summary),
        .sticky_faults(sticky_faults),
        .irq_pending(irq_pending)
    );

    adaptive_aero_request_supervisor u_supervisor (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_global_enable(cfg_global_enable),
        .cfg_release_enable(cfg_release_enable),
        .cfg_clear_faults(cfg_clear_faults),
        .cfg_request_launch(cfg_request_launch),
        .cfg_mode_sel(cfg_mode_sel),
        .cfg_timeout_threshold(cfg_timeout_threshold),
        .cfg_stale_age_threshold(cfg_stale_age_threshold),
        .cfg_request_payload(cfg_request_payload),
        .model_req_valid(model_req_valid),
        .model_req_data(model_req_data),
        .model_req_ready(model_req_ready),
        .model_rsp_valid(model_rsp_valid),
        .model_rsp_data(model_rsp_data),
        .model_rsp_ready(model_rsp_ready),
        .busy(busy),
        .response_ready(response_ready),
        .stale_rejected(stale_rejected),
        .timeout_fault(timeout_fault),
        .invalid_response(invalid_response),
        .sequence_mismatch(sequence_mismatch),
        .accepted_response_summary(accepted_response_summary),
        .current_sequence_id(current_sequence_id),
        .request_timestamp(request_timestamp),
        .sticky_fault_set(sticky_faults),
        .fault_event_pulse(fault_event_pulse)
    );

    adaptive_aero_actuator_control u_actuator (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_global_enable(cfg_global_enable),
        .cfg_release_enable(cfg_release_enable),
        .cfg_actuator_min_limit(cfg_actuator_min_limit),
        .cfg_actuator_max_limit(cfg_actuator_max_limit),
        .cfg_actuator_rate_limit(cfg_actuator_rate_limit),
        .accepted_response_summary(accepted_response_summary),
        .response_ready(response_ready),
        .busy(busy),
        .stale_rejected(stale_rejected),
        .timeout_fault(timeout_fault),
        .invalid_response(invalid_response),
        .sequence_mismatch(sequence_mismatch),
        .fault_event_pulse(fault_event_pulse),
        .actuator_cmd_valid(actuator_cmd_valid),
        .actuator_cmd_ready(actuator_cmd_ready),
        .actuator_cmd_data(actuator_cmd_data),
        .last_accepted_command(last_accepted_command),
        .clamp_applied(clamp_applied),
        .fallback_active(fallback_active)
    );
assign status_busy = busy;
assign status_response_ready = response_ready;
assign status_stale_rejected = stale_rejected;
assign status_timeout_fault = timeout_fault;
assign status_invalid_response = invalid_response;
assign status_sequence_mismatch = sequence_mismatch;
assign last_response_summary = accepted_response_summary;
assign irq_pending = fault_event_pulse;
assign status_clamp_applied = clamp_applied;
assign status_fallback_active = fallback_active;

endmodule
