module safety_fault_watchdog_controller (
    clk,
    reset_n,
    control_enable,
    watchdog_enable,
    irq_enable,
    fault_clear_pulse,
    irq_clear_pulse,
    watchdog_timeout_cfg,
    fault_mask_cfg,
    escalation_policy_cfg,
    heartbeat,
    fault_in,
    external_reset_done,
    reset_count_value,
    heartbeat_count_value,
    fault_status_value,
    irq_status_value,
    status_healthy,
    status_watchdog_expired,
    status_fault_pending,
    status_reset_requested,
    status_escalation_active,
    watchdog_expired_latched,
    reset_requested_latched,
    escalation_level_value,
    reset_request,
    safety_irq,
    fault_latched,
    watchdog_expired
);

input clk;
input reset_n;
input control_enable;
input watchdog_enable;
input irq_enable;
input fault_clear_pulse;
input [3:0] irq_clear_pulse;
input [31:0] watchdog_timeout_cfg;
input [7:0] fault_mask_cfg;
input [31:0] escalation_policy_cfg;
input heartbeat;
input [7:0] fault_in;
input external_reset_done;
output reg [31:0] reset_count_value;
output reg [31:0] heartbeat_count_value;
output reg [7:0] fault_status_value;
output reg [3:0] irq_status_value;
output reg status_healthy;
output reg status_watchdog_expired;
output reg status_fault_pending;
output reg status_reset_requested;
output reg status_escalation_active;
output reg watchdog_expired_latched;
output reg reset_requested_latched;
output reg [1:0] escalation_level_value;
output reg reset_request;
output reg safety_irq;
output reg [7:0] fault_latched;
output reg watchdog_expired;

reg [31:0] watchdog_counter;
reg [7:0] fault_events;
reg [7:0] watchdog_events;
reg [31:0] event_score;
reg [7:0] masked_faults;
reg [1:0] next_escalation_level;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        reset_count_value <= 32'h00000000;
        heartbeat_count_value <= 32'h00000000;
        fault_status_value <= 8'h00;
        irq_status_value <= 4'b0000;
        status_healthy <= 1'b1;
        status_watchdog_expired <= 1'b0;
        status_fault_pending <= 1'b0;
        status_reset_requested <= 1'b0;
        status_escalation_active <= 1'b0;
        watchdog_expired_latched <= 1'b0;
        reset_requested_latched <= 1'b0;
        escalation_level_value <= 2'b00;
        reset_request <= 1'b0;
        safety_irq <= 1'b0;
        fault_latched <= 8'h00;
        watchdog_expired <= 1'b0;
        watchdog_counter <= 32'h00000000;
        fault_events <= 8'h00;
        watchdog_events <= 8'h00;
        event_score <= 32'h00000000;
    end else begin
        masked_faults <= fault_in & fault_mask_cfg;
        if (heartbeat) heartbeat_count_value <= heartbeat_count_value + 32'd1;
        if (control_enable && watchdog_enable) begin
            if (heartbeat) watchdog_counter <= watchdog_timeout_cfg;
            else if (watchdog_counter != 32'h00000000) watchdog_counter <= watchdog_counter - 32'd1;
            else watchdog_counter <= 32'h00000000;
        end else begin
            watchdog_counter <= watchdog_timeout_cfg;
        end
        if (control_enable && watchdog_enable && (watchdog_timeout_cfg != 32'h00000000) && (watchdog_counter == 32'h00000000) && !heartbeat) begin
            watchdog_expired_latched <= 1'b1;
            watchdog_expired <= 1'b1;
            irq_status_value[0] <= 1'b1;
            watchdog_events <= watchdog_events + 8'd1;
            event_score <= event_score + 32'd1;
        end
        if (|masked_faults) begin
            fault_latched <= fault_latched | masked_faults;
            fault_status_value <= fault_status_value | masked_faults;
            irq_status_value[1] <= 1'b1;
            fault_events <= fault_events + 8'd1;
            event_score <= event_score + 32'd1;
        end
        if (fault_clear_pulse) begin
            fault_latched <= 8'h00;
            fault_status_value <= 8'h00;
            irq_status_value[1] <= 1'b0;
        end
        if (irq_clear_pulse[0]) irq_status_value[0] <= 1'b0;
        if (irq_clear_pulse[1]) irq_status_value[1] <= 1'b0;
        if (irq_clear_pulse[2]) irq_status_value[2] <= 1'b0;
        if (irq_clear_pulse[3]) irq_status_value[3] <= 1'b0;
        next_escalation_level = 2'b00;
        if (event_score >= {24'h000000, escalation_policy_cfg[7:0]}) next_escalation_level = 2'b01;
        if (event_score >= {24'h000000, escalation_policy_cfg[15:8]}) next_escalation_level = 2'b10;
        if (event_score >= {24'h000000, escalation_policy_cfg[23:16]}) next_escalation_level = 2'b11;
        escalation_level_value <= next_escalation_level;
        if (next_escalation_level >= 2'b10) begin
            reset_request <= 1'b1;
            irq_status_value[2] <= 1'b1;
            if (!reset_requested_latched) reset_count_value <= reset_count_value + 32'd1;
            reset_requested_latched <= 1'b1;
        end
        if (next_escalation_level != 2'b00) irq_status_value[3] <= 1'b1;
        if (external_reset_done) begin
            reset_request <= 1'b0;
            reset_requested_latched <= 1'b0;
            irq_status_value[2] <= 1'b0;
        end
        status_watchdog_expired <= watchdog_expired_latched;
        status_fault_pending <= (fault_latched != 8'h00);
        status_reset_requested <= reset_request;
        status_escalation_active <= (next_escalation_level != 2'b00);
        status_healthy <= ~(status_watchdog_expired | status_fault_pending | status_reset_requested | status_escalation_active);
        safety_irq <= irq_enable & |irq_status_value;
    end
end

endmodule
