module adaptive_aero_control_top (
    input             clk,
    input             reset_n,
    input      [31:0] wb_adr_i,
    input      [31:0] wb_dat_i,
    output     [31:0] wb_dat_o,
    input      [3:0] wb_sel_i,
    input             wb_cyc_i,
    input             wb_stb_i,
    input             wb_we_i,
    output            wb_ack_o,
    output            wb_err_o,
    output            wb_rty_o,
    output            irq_o,
    output            req_valid_o,
    input             req_ready_i,
    output     [63:0] req_data_o,
    input             resp_valid_i,
    output            resp_ready_o,
    input      [63:0] resp_data_i,
    output     [15:0] actuator_cmd_o,
    output            actuator_valid_o,
    output            fault_o,
    output            safe_state_o,
    output            uart_tx_o,
    input             uart_rx_i
);
wire [1:0] cfg_mode;
wire cfg_cmd_valid;
wire [15:0] cfg_velocity_q8_8;
wire [15:0] cfg_geometry_handle;
wire [15:0] cfg_request_seq;
wire [15:0] cfg_timeout_threshold;
wire [15:0] cfg_actuator_min;
wire [15:0] cfg_actuator_max;
wire [15:0] cfg_actuator_slew;
wire [15:0] cfg_velocity_low_limit;
wire [15:0] cfg_velocity_high_limit;
wire [15:0] cfg_safe_state_cmd;
wire cfg_hold_last_safe;
wire [7:0] cfg_irq_enable;
wire cfg_fault_clear;
wire cfg_irq_ack;
wire status_outstanding_req;
wire [15:0] status_last_accepted_seq;
wire [15:0] status_response_seq;
wire [15:0] status_timeout_count;
wire [15:0] status_stale_reject_count;
wire [15:0] status_invalid_env_count;
wire [7:0] status_fault_code;
wire status_safe_state;
wire status_fault_latched;
wire [7:0] status_irq_sticky;
wire [15:0] status_actuator_cmd;
wire status_actuator_valid;
wire [15:0] status_age_counter;
wire [63:0] status_last_req_word;
wire [63:0] status_last_resp_word;
    wire fifo_rd_dummy_full;
    wire fifo_rd_dummy_empty;
    wire [4:0] fifo_rd_dummy_count;

wire fifo_wr_en;
wire fifo_rd_en;
wire [63:0] fifo_wr_data;
wire [63:0] fifo_rd_data;
    adaptive_aero_control_mmio u_mmio (
        .clk(clk),
        .reset_n(reset_n),
        .wb_adr_i(wb_adr_i),
        .wb_dat_i(wb_dat_i),
        .wb_dat_o(wb_dat_o),
        .wb_sel_i(wb_sel_i),
        .wb_cyc_i(wb_cyc_i),
        .wb_stb_i(wb_stb_i),
        .wb_we_i(wb_we_i),
        .wb_ack_o(wb_ack_o),
        .wb_err_o(wb_err_o),
        .wb_rty_o(wb_rty_o),
        .cfg_mode(cfg_mode),
        .cfg_cmd_valid(cfg_cmd_valid),
        .cfg_velocity_q8_8(cfg_velocity_q8_8),
        .cfg_geometry_handle(cfg_geometry_handle),
        .cfg_request_seq(cfg_request_seq),
        .cfg_timeout_threshold(cfg_timeout_threshold),
        .cfg_actuator_min(cfg_actuator_min),
        .cfg_actuator_max(cfg_actuator_max),
        .cfg_actuator_slew(cfg_actuator_slew),
        .cfg_velocity_low_limit(cfg_velocity_low_limit),
        .cfg_velocity_high_limit(cfg_velocity_high_limit),
        .cfg_safe_state_cmd(cfg_safe_state_cmd),
        .cfg_hold_last_safe(cfg_hold_last_safe),
        .cfg_irq_enable(cfg_irq_enable),
        .cfg_fault_clear(cfg_fault_clear),
        .cfg_irq_ack(cfg_irq_ack),
        .status_outstanding_req(status_outstanding_req),
        .status_last_accepted_seq(status_last_accepted_seq),
        .status_response_seq(status_response_seq),
        .status_timeout_count(status_timeout_count),
        .status_stale_reject_count(status_stale_reject_count),
        .status_invalid_env_count(status_invalid_env_count),
        .status_fault_code(status_fault_code),
        .status_safe_state(status_safe_state),
        .status_fault_latched(status_fault_latched),
        .status_irq_sticky(status_irq_sticky),
        .status_actuator_cmd(status_actuator_cmd),
        .status_actuator_valid(status_actuator_valid),
        .status_age_counter(status_age_counter),
        .status_last_req_word(status_last_req_word),
        .status_last_resp_word(status_last_resp_word)
    );

    adaptive_aero_control_core u_core (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_mode(cfg_mode),
        .cfg_cmd_valid(cfg_cmd_valid),
        .cfg_velocity_q8_8(cfg_velocity_q8_8),
        .cfg_geometry_handle(cfg_geometry_handle),
        .cfg_request_seq(cfg_request_seq),
        .cfg_timeout_threshold(cfg_timeout_threshold),
        .cfg_actuator_min(cfg_actuator_min),
        .cfg_actuator_max(cfg_actuator_max),
        .cfg_actuator_slew(cfg_actuator_slew),
        .cfg_velocity_low_limit(cfg_velocity_low_limit),
        .cfg_velocity_high_limit(cfg_velocity_high_limit),
        .cfg_safe_state_cmd(cfg_safe_state_cmd),
        .cfg_hold_last_safe(cfg_hold_last_safe),
        .cfg_irq_enable(cfg_irq_enable),
        .cfg_fault_clear(cfg_fault_clear),
        .cfg_irq_ack(cfg_irq_ack),
        .req_ready_i(req_ready_i),
        .req_valid_o(req_valid_o),
        .req_data_o(req_data_o),
        .resp_valid_i(resp_valid_i),
        .resp_ready_o(resp_ready_o),
        .resp_data_i(resp_data_i),
        .status_outstanding_req(status_outstanding_req),
        .status_last_accepted_seq(status_last_accepted_seq),
        .status_response_seq(status_response_seq),
        .status_timeout_count(status_timeout_count),
        .status_stale_reject_count(status_stale_reject_count),
        .status_invalid_env_count(status_invalid_env_count),
        .status_fault_code(status_fault_code),
        .status_safe_state(status_safe_state),
        .status_fault_latched(status_fault_latched),
        .status_irq_sticky(status_irq_sticky),
        .status_actuator_cmd(status_actuator_cmd),
        .status_actuator_valid(status_actuator_valid),
        .status_age_counter(status_age_counter),
        .status_last_req_word(status_last_req_word),
        .status_last_resp_word(status_last_resp_word),
        .actuator_cmd_o(actuator_cmd_o),
        .actuator_valid_o(actuator_valid_o),
        .fault_o(fault_o),
        .safe_state_o(safe_state_o),
        .irq_o(irq_o)
    );

    control_token_fifo_wrapper u_fifo (
        .clk(clk),
        .reset_n(reset_n),
        .wr_en(req_valid_o),
        .rd_en(resp_ready_o),
        .wr_data(req_data_o),
        .rd_data(),
        .full(fifo_rd_dummy_full),
        .empty(fifo_rd_dummy_empty),
        .count(fifo_rd_dummy_count)
    );

    assign uart_tx_o = wb_rty_o;
endmodule
