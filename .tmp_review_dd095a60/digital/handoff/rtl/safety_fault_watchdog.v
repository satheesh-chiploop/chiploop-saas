module safety_fault_watchdog (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    heartbeat,
    fault_in,
    external_reset_done,
    rd_data,
    safety_irq,
    reset_request,
    fault_latched,
    escalation_level,
    watchdog_expired
);

input clk;
input reset_n;
input wr_en;
input [11:0] wr_addr;
input [31:0] wr_data;
input rd_en;
input [11:0] rd_addr;
input heartbeat;
input [7:0] fault_in;
input external_reset_done;
output [31:0] rd_data;
output safety_irq;
output reset_request;
output [7:0] fault_latched;
output [1:0] escalation_level;
output watchdog_expired;

wire control_enable;
wire watchdog_enable;
wire irq_enable;
wire fault_clear_pulse;
wire [3:0] irq_clear_pulse;
wire [31:0] watchdog_timeout_cfg;
wire [7:0] fault_mask_cfg;
wire [31:0] escalation_policy_cfg;
wire [31:0] mmio_rd_data;
wire [31:0] reset_count_value;
wire [31:0] heartbeat_count_value;
wire [7:0] fault_status_value;
wire [3:0] irq_status_value;
wire status_healthy;
wire status_watchdog_expired;
wire status_fault_pending;
wire status_reset_requested;
wire status_escalation_active;
wire watchdog_expired_latched;
wire reset_requested_latched;
wire [1:0] escalation_level_value;
wire safety_fault_watchdog_mmio_control_enable;
wire [1:0] safety_fault_watchdog_controller_escalation_level_value;
wire [31:0] safety_fault_watchdog_mmio_escalation_policy_cfg;
wire safety_fault_watchdog_mmio_fault_clear_pulse;
wire [7:0] safety_fault_watchdog_mmio_fault_mask_cfg;
wire [7:0] safety_fault_watchdog_controller_fault_status_value;
wire [31:0] safety_fault_watchdog_controller_heartbeat_count_value;
wire [3:0] safety_fault_watchdog_mmio_irq_clear_pulse;
wire safety_fault_watchdog_mmio_irq_enable;
wire [3:0] safety_fault_watchdog_controller_irq_status_value;
wire [31:0] safety_fault_watchdog_controller_reset_count_value;
wire safety_fault_watchdog_controller_reset_requested_latched;
wire safety_fault_watchdog_controller_status_escalation_active;
wire safety_fault_watchdog_controller_status_fault_pending;
wire safety_fault_watchdog_controller_status_healthy;
wire safety_fault_watchdog_controller_status_reset_requested;
wire safety_fault_watchdog_controller_status_watchdog_expired;
wire safety_fault_watchdog_mmio_watchdog_enable;
wire safety_fault_watchdog_controller_watchdog_expired_latched;
wire [31:0] safety_fault_watchdog_mmio_watchdog_timeout_cfg;
assign rd_data = mmio_rd_data;
assign escalation_level = escalation_level_value;

safety_fault_watchdog_mmio u_safety_fault_watchdog_mmio (
    .clk(clk),
    .reset_n(reset_n),
    .wr_en(wr_en),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_addr(rd_addr),
    .heartbeat(heartbeat),
    .fault_in(fault_in),
    .external_reset_done(external_reset_done),
    .control_enable(control_enable),
    .watchdog_enable(watchdog_enable),
    .irq_enable(irq_enable),
    .fault_clear_pulse(fault_clear_pulse),
    .irq_clear_pulse(irq_clear_pulse),
    .watchdog_timeout_cfg(watchdog_timeout_cfg),
    .fault_mask_cfg(fault_mask_cfg),
    .escalation_policy_cfg(escalation_policy_cfg),
    .rd_data(mmio_rd_data),
    .reset_count_value(reset_count_value),
    .heartbeat_count_value(heartbeat_count_value),
    .fault_status_value(fault_status_value),
    .irq_status_value(irq_status_value),
    .status_healthy(status_healthy),
    .status_watchdog_expired(status_watchdog_expired),
    .status_fault_pending(status_fault_pending),
    .status_reset_requested(status_reset_requested),
    .status_escalation_active(status_escalation_active),
    .watchdog_expired_latched(watchdog_expired_latched),
    .reset_requested_latched(reset_requested_latched),
    .escalation_level_value(escalation_level_value)
);

safety_fault_watchdog_controller u_safety_fault_watchdog_controller (
    .clk(clk),
    .reset_n(reset_n),
    .control_enable(control_enable),
    .watchdog_enable(watchdog_enable),
    .irq_enable(irq_enable),
    .fault_clear_pulse(fault_clear_pulse),
    .irq_clear_pulse(irq_clear_pulse),
    .watchdog_timeout_cfg(watchdog_timeout_cfg),
    .fault_mask_cfg(fault_mask_cfg),
    .escalation_policy_cfg(escalation_policy_cfg),
    .heartbeat(heartbeat),
    .fault_in(fault_in),
    .external_reset_done(external_reset_done),
    .reset_count_value(reset_count_value),
    .heartbeat_count_value(heartbeat_count_value),
    .fault_status_value(fault_status_value),
    .irq_status_value(irq_status_value),
    .status_healthy(status_healthy),
    .status_watchdog_expired(status_watchdog_expired),
    .status_fault_pending(status_fault_pending),
    .status_reset_requested(status_reset_requested),
    .status_escalation_active(status_escalation_active),
    .watchdog_expired_latched(watchdog_expired_latched),
    .reset_requested_latched(reset_requested_latched),
    .escalation_level_value(escalation_level_value),
    .reset_request(reset_request),
    .safety_irq(safety_irq),
    .fault_latched(fault_latched),
    .watchdog_expired(watchdog_expired)
);

endmodule
