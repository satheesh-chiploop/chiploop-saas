module safety_fault_watchdog_mmio (
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
    control_enable,
    watchdog_enable,
    irq_enable,
    fault_clear_pulse,
    irq_clear_pulse,
    watchdog_timeout_cfg,
    fault_mask_cfg,
    escalation_policy_cfg,
    rd_data,
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
    escalation_level_value
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
output reg control_enable;
output reg watchdog_enable;
output reg irq_enable;
output reg fault_clear_pulse;
output reg [3:0] irq_clear_pulse;
output reg [31:0] watchdog_timeout_cfg;
output reg [7:0] fault_mask_cfg;
output reg [31:0] escalation_policy_cfg;
output reg [31:0] rd_data;
input [31:0] reset_count_value;
input [31:0] heartbeat_count_value;
input [7:0] fault_status_value;
input [3:0] irq_status_value;
input status_healthy;
input status_watchdog_expired;
input status_fault_pending;
input status_reset_requested;
input status_escalation_active;
input watchdog_expired_latched;
input reset_requested_latched;
input [1:0] escalation_level_value;
reg [31:0] control_reg;
reg [31:0] status_reg;
reg [31:0] irq_clear_reg;
reg [31:0] read_mux;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 32'h00000000;
        watchdog_timeout_cfg <= 32'h00000000;
        fault_mask_cfg <= 8'h00;
        escalation_policy_cfg <= 32'h00000000;
        irq_clear_reg <= 32'h00000000;
        control_enable <= 1'b0;
        watchdog_enable <= 1'b0;
        irq_enable <= 1'b0;
        fault_clear_pulse <= 1'b0;
        irq_clear_pulse <= 4'b0000;
    end else begin
        control_reg <= wr_en && (wr_addr == 12'h000) ? wr_data : control_reg;
        watchdog_timeout_cfg <= wr_en && (wr_addr == 12'h008) ? wr_data : watchdog_timeout_cfg;
        fault_mask_cfg <= wr_en && (wr_addr == 12'h010) ? wr_data[7:0] : fault_mask_cfg;
        escalation_policy_cfg <= wr_en && (wr_addr == 12'h018) ? wr_data : escalation_policy_cfg;
        irq_clear_reg <= wr_en && (wr_addr == 12'h024) ? wr_data : irq_clear_reg;
        control_enable <= (wr_en && (wr_addr == 12'h000) && wr_data[0]) ? 1'b1 : ((wr_en && (wr_addr == 12'h000) && !wr_data[0]) ? 1'b0 : control_enable);
        watchdog_enable <= (wr_en && (wr_addr == 12'h000) && wr_data[1]) ? 1'b1 : ((wr_en && (wr_addr == 12'h000) && !wr_data[1]) ? 1'b0 : watchdog_enable);
        irq_enable <= (wr_en && (wr_addr == 12'h000) && wr_data[2]) ? 1'b1 : ((wr_en && (wr_addr == 12'h000) && !wr_data[2]) ? 1'b0 : irq_enable);
        fault_clear_pulse <= (wr_en && (wr_addr == 12'h000) && wr_data[3]) ? 1'b1 : 1'b0;
        irq_clear_pulse <= (wr_en && (wr_addr == 12'h024)) ? wr_data[3:0] : 4'b0000;
    end
end

always @(*) begin
    status_reg = 32'h00000000;
    status_reg[0] = status_healthy;
    status_reg[1] = status_watchdog_expired;
    status_reg[2] = status_fault_pending;
    status_reg[3] = status_reset_requested;
    status_reg[4] = status_escalation_active;
    read_mux = 32'h00000000;
    if (rd_en) begin
        case (rd_addr)
            12'h000: read_mux = control_reg;
            12'h004: read_mux = status_reg;
            12'h008: read_mux = watchdog_timeout_cfg;
            12'h00C: read_mux = heartbeat_count_value;
            12'h010: read_mux = {24'h000000, fault_mask_cfg};
            12'h014: read_mux = {24'h000000, fault_status_value};
            12'h018: read_mux = escalation_policy_cfg;
            12'h01C: read_mux = {30'h00000000, escalation_level_value};
            12'h020: read_mux = {28'h0000000, irq_status_value};
            12'h024: read_mux = irq_clear_reg;
            12'h028: read_mux = reset_count_value;
            default: read_mux = 32'h00000000;
        endcase
    end else begin
        read_mux = 32'h00000000;
    end
    rd_data = read_mux;
end

endmodule
