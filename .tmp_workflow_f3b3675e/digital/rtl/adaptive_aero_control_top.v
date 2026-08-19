module adaptive_aero_control_top (
    clk,
    rst_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_sel_i,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_ack_o,
    wb_err_o,
    irq,
    actuator_cmd,
    actuator_valid,
    actuator_ready
);

input clk;
input rst_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input [3:0] wb_sel_i;
input wb_cyc_i;
input wb_stb_i;
input wb_we_i;
output wb_ack_o;
output wb_err_o;
output irq;
output [31:0] actuator_cmd;
output actuator_valid;
input actuator_ready;
wire reg_control_enable;
wire reg_control_clear_faults;
wire reg_control_arm_safe_fallback;
wire reg_control_bypass_output_hold;
wire [3:0] reg_control_mode;
wire [31:0] reg_seq_in;
wire [31:0] reg_age_limit;
wire [31:0] reg_velocity_mps;
wire [31:0] reg_act_min;
wire [31:0] reg_act_max;
wire [31:0] reg_act_cmd;
wire reg_irq_ack;
wire status_busy;
wire status_command_accepted;
wire status_stale_rejected;
wire status_timeout_fault;
wire status_invalid_input;
wire status_clamp_applied;
wire status_safe_fallback_active;
wire status_irq_pending;
wire [31:0] reg_last_good;
wire [31:0] reg_timeout_cnt;
wire [31:0] reg_fault_cause;
adaptive_aero_control_mmio u_adaptive_aero_control_mmio (
    .clk(clk),
    .rst_n(rst_n),
    .wb_adr_i(wb_adr_i),
    .wb_dat_i(wb_dat_i),
    .wb_dat_o(wb_dat_o),
    .wb_sel_i(wb_sel_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .wb_ack_o(wb_ack_o),
    .wb_err_o(wb_err_o),
    .reg_control_enable(reg_control_enable),
    .reg_control_clear_faults(reg_control_clear_faults),
    .reg_control_arm_safe_fallback(reg_control_arm_safe_fallback),
    .reg_control_bypass_output_hold(reg_control_bypass_output_hold),
    .reg_control_mode(reg_control_mode),
    .reg_seq_in(reg_seq_in),
    .reg_age_limit(reg_age_limit),
    .reg_velocity_mps(reg_velocity_mps),
    .reg_act_min(reg_act_min),
    .reg_act_max(reg_act_max),
    .reg_act_cmd(reg_act_cmd),
    .reg_irq_ack(reg_irq_ack),
    .status_busy(status_busy),
    .status_command_accepted(status_command_accepted),
    .status_stale_rejected(status_stale_rejected),
    .status_timeout_fault(status_timeout_fault),
    .status_invalid_input(status_invalid_input),
    .status_clamp_applied(status_clamp_applied),
    .status_safe_fallback_active(status_safe_fallback_active),
    .status_irq_pending(status_irq_pending),
    .reg_last_good(reg_last_good),
    .reg_timeout_cnt(reg_timeout_cnt),
    .reg_fault_cause(reg_fault_cause)
);

adaptive_aero_control_core u_adaptive_aero_control_core (
    .clk(clk),
    .rst_n(rst_n),
    .reg_control_enable(reg_control_enable),
    .reg_control_clear_faults(reg_control_clear_faults),
    .reg_control_arm_safe_fallback(reg_control_arm_safe_fallback),
    .reg_control_bypass_output_hold(reg_control_bypass_output_hold),
    .reg_control_mode(reg_control_mode),
    .reg_seq_in(reg_seq_in),
    .reg_age_limit(reg_age_limit),
    .reg_velocity_mps(reg_velocity_mps),
    .reg_act_min(reg_act_min),
    .reg_act_max(reg_act_max),
    .reg_act_cmd(reg_act_cmd),
    .reg_irq_ack(reg_irq_ack),
    .status_busy(status_busy),
    .status_command_accepted(status_command_accepted),
    .status_stale_rejected(status_stale_rejected),
    .status_timeout_fault(status_timeout_fault),
    .status_invalid_input(status_invalid_input),
    .status_clamp_applied(status_clamp_applied),
    .status_safe_fallback_active(status_safe_fallback_active),
    .status_irq_pending(status_irq_pending),
    .reg_last_good(reg_last_good),
    .reg_timeout_cnt(reg_timeout_cnt),
    .reg_fault_cause(reg_fault_cause),
    .actuator_cmd(actuator_cmd),
    .actuator_valid(actuator_valid),
    .actuator_ready(actuator_ready),
    .irq(irq)
);

endmodule
