module adaptive_aero_control_top (
    input         clk,
    input         reset_n,
    input         in_cmd_valid,
    input  [63:0] in_cmd_data,
    output        in_cmd_ready,
    output        out_act_valid,
    output [63:0] out_act_data,
    input         out_act_ready,
    output        model_req_valid,
    output [63:0] model_req_data,
    input         model_req_ready,
    input         model_rsp_valid,
    input  [63:0] model_rsp_data,
    output        model_rsp_ready,
    input         cfg_valid,
    input         cfg_write,
    input  [3:0] cfg_addr,
    input  [31:0] cfg_wdata,
    output [31:0] cfg_rdata,
    output        cfg_ready,
    output        status_valid,
    output [31:0] status_data
);
wire control_register_bank_enable;
wire [15:0] control_register_bank_timeout_limit_cycles;
wire [7:0] control_register_bank_sequence_window;
wire [15:0] control_register_bank_actuator_min;
wire [15:0] control_register_bank_actuator_max;
wire [15:0] control_register_bank_fallback_command;
wire control_register_bank_slew_limit_enable;
wire [7:0] control_register_bank_slew_limit;
wire        control_register_bank_clear_sticky_status;
wire [31:0] status_telemetry_status_image;
wire stream_rx_packet_accept;
wire stream_rx_packet_error;
wire [7:0] stream_rx_sequence_id;
wire [7:0] stream_rx_age_counter;
wire [15:0] stream_rx_command_value;
wire [3:0] stream_rx_command_mode;
wire [7:0] stream_rx_fault_flags;
wire stream_rx_checksum_ok;
wire command_validator_valid_command_seen;
wire command_validator_stale_reject;
wire command_validator_checksum_fault;
wire command_validator_parser_error;
wire [15:0] command_validator_validated_command_value;
wire [3:0] command_validator_validated_command_mode;
wire [7:0]  command_validator_validated_fault_flags;
wire [7:0]  command_validator_validated_sequence_id;
wire [7:0]  command_validator_validated_age_counter;
wire [7:0]  command_validator_last_accepted_sequence;
wire timeout_monitor_timeout_fault;
wire timeout_monitor_wait_active;
wire [15:0] timeout_monitor_timeout_counter;
wire [15:0] actuator_clamper_clamped_command_value;
wire actuator_clamper_clamp_active;
wire        actuator_clamper_slew_active;
wire [15:0] actuator_clamper_updated_previous_command_value;
wire [1:0]  fallback_fsm_fallback_state;
wire [15:0] fallback_fsm_final_command_value;
wire [3:0] fallback_fsm_final_command_mode;
wire [7:0] fallback_fsm_safety_flags;
wire fallback_fsm_fallback_active;
wire actuator_tx_request_pending;
wire actuator_tx_fresh_command_event;
assign status_data = status_telemetry_status_image;

control_register_bank u_control_register_bank (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_valid(cfg_valid),
    .cfg_write(cfg_write),
    .cfg_addr(cfg_addr),
    .cfg_wdata(cfg_wdata),
    .cfg_rdata(cfg_rdata),
    .cfg_ready(cfg_ready),
    .enable(control_register_bank_enable),
    .timeout_limit_cycles(control_register_bank_timeout_limit_cycles),
    .sequence_window(control_register_bank_sequence_window),
    .actuator_min(control_register_bank_actuator_min),
    .actuator_max(control_register_bank_actuator_max),
    .fallback_command(control_register_bank_fallback_command),
    .slew_limit_enable(control_register_bank_slew_limit_enable),
    .slew_limit(control_register_bank_slew_limit),
    .clear_sticky_status(control_register_bank_clear_sticky_status),
    .status_image(status_telemetry_status_image)
);

stream_rx u_stream_rx (
    .clk(clk),
    .reset_n(reset_n),
    .in_cmd_valid(in_cmd_valid),
    .in_cmd_data(in_cmd_data),
    .in_cmd_ready(in_cmd_ready),
    .packet_accept(stream_rx_packet_accept),
    .packet_error(stream_rx_packet_error),
    .sequence_id(stream_rx_sequence_id),
    .age_counter(stream_rx_age_counter),
    .command_value(stream_rx_command_value),
    .command_mode(stream_rx_command_mode),
    .fault_flags(stream_rx_fault_flags),
    .checksum_ok(stream_rx_checksum_ok)
);

command_validator u_command_validator (
    .clk(clk),
    .reset_n(reset_n),
    .packet_accept(stream_rx_packet_accept),
    .packet_error(stream_rx_packet_error),
    .sequence_id(stream_rx_sequence_id),
    .age_counter(stream_rx_age_counter),
    .command_value(stream_rx_command_value),
    .command_mode(stream_rx_command_mode),
    .fault_flags(stream_rx_fault_flags),
    .checksum_ok(stream_rx_checksum_ok),
    .sequence_window(control_register_bank_sequence_window),
    .last_accepted_sequence(command_validator_last_accepted_sequence),
    .valid_command_seen(command_validator_valid_command_seen),
    .stale_reject(command_validator_stale_reject),
    .checksum_fault(command_validator_checksum_fault),
    .parser_error(command_validator_parser_error),
    .validated_command_value(command_validator_validated_command_value),
    .validated_command_mode(command_validator_validated_command_mode),
    .validated_fault_flags(command_validator_validated_fault_flags),
    .validated_sequence_id(command_validator_validated_sequence_id),
    .validated_age_counter(command_validator_validated_age_counter)
);

timeout_monitor u_timeout_monitor (
    .clk(clk),
    .reset_n(reset_n),
    .enable(control_register_bank_enable),
    .valid_command_seen(command_validator_valid_command_seen),
    .request_pending(actuator_tx_request_pending),
    .fresh_command_event(actuator_tx_fresh_command_event),
    .timeout_limit_cycles(control_register_bank_timeout_limit_cycles),
    .timeout_fault(timeout_monitor_timeout_fault),
    .wait_active(timeout_monitor_wait_active),
    .timeout_counter(timeout_monitor_timeout_counter)
);

actuator_clamper u_actuator_clamper (
    .clk(clk),
    .reset_n(reset_n),
    .validated_command_value(command_validator_validated_command_value),
    .validated_command_mode(command_validator_validated_command_mode),
    .actuator_min(control_register_bank_actuator_min),
    .actuator_max(control_register_bank_actuator_max),
    .slew_limit_enable(control_register_bank_slew_limit_enable),
    .slew_limit(control_register_bank_slew_limit),
    .previous_command_value(actuator_clamper_updated_previous_command_value),
    .clamped_command_value(actuator_clamper_clamped_command_value),
    .clamp_active(actuator_clamper_clamp_active),
    .slew_active(actuator_clamper_slew_active),
    .updated_previous_command_value(actuator_clamper_updated_previous_command_value)
);

fallback_fsm u_fallback_fsm (
    .clk(clk),
    .reset_n(reset_n),
    .enable(control_register_bank_enable),
    .valid_command_seen(command_validator_valid_command_seen),
    .stale_reject(command_validator_stale_reject),
    .checksum_fault(command_validator_checksum_fault),
    .parser_error(command_validator_parser_error),
    .timeout_fault(timeout_monitor_timeout_fault),
    .clamp_active(actuator_clamper_clamp_active),
    .wait_active(timeout_monitor_wait_active),
    .last_good_sequence(command_validator_last_accepted_sequence),
    .clamped_command_value(actuator_clamper_clamped_command_value),
    .validated_command_mode(command_validator_validated_command_mode),
    .fallback_command(control_register_bank_fallback_command),
    .hold_last_good_enable(control_register_bank_clear_sticky_status ? 1'b0 : 1'b0),
    .freshness_ok(command_validator_valid_command_seen),
    .fallback_state(fallback_fsm_fallback_state),
    .final_command_value(fallback_fsm_final_command_value),
    .final_command_mode(fallback_fsm_final_command_mode),
    .safety_flags(fallback_fsm_safety_flags),
    .fallback_active(fallback_fsm_fallback_active)
);

actuator_tx u_actuator_tx (
    .clk(clk),
    .reset_n(reset_n),
    .final_command_value(fallback_fsm_final_command_value),
    .final_command_mode(fallback_fsm_final_command_mode),
    .safety_flags(fallback_fsm_safety_flags),
    .fallback_active(fallback_fsm_fallback_active),
    .out_act_ready(out_act_ready),
    .out_act_valid(out_act_valid),
    .out_act_data(out_act_data),
    .request_pending(actuator_tx_request_pending),
    .fresh_command_event(actuator_tx_fresh_command_event),
    .model_req_valid(model_req_valid),
    .model_req_data(model_req_data),
    .model_req_ready(model_req_ready),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(model_rsp_ready)
);

status_telemetry u_status_telemetry (
    .clk(clk),
    .reset_n(reset_n),
    .enable(control_register_bank_enable),
    .valid_command_seen(command_validator_valid_command_seen),
    .stale_reject(command_validator_stale_reject),
    .timeout_fault(timeout_monitor_timeout_fault),
    .checksum_fault(command_validator_checksum_fault),
    .clamp_active(actuator_clamper_clamp_active),
    .fallback_active(fallback_fsm_fallback_active),
    .last_good_sequence(command_validator_last_accepted_sequence),
    .status_image(status_telemetry_status_image),
    .status_valid(status_valid)
);

endmodule
