module adaptive_aero_control_mmio (
    clk,
    rst_n,
    mmio_addr,
    mmio_wdata,
    mmio_write,
    mmio_valid,
    mmio_rdata,
    mmio_ready,
    cfg_timeout_limit,
    cfg_seq_policy,
    cfg_control_mode_permit,
    cfg_act_min,
    cfg_act_max,
    cfg_safe_min,
    cfg_safe_max,
    cfg_irq_enable,
    cfg_clear_sticky_faults,
    cmd_valid,
    cmd_id,
    cmd_seq,
    cmd_age_ts,
    cmd_control_mode,
    cmd_act_pos,
    cmd_integrity,
    accepted_event,
    rejected_event,
    stale_data_fault,
    timeout_fault,
    clamp_applied,
    fallback_active,
    sequence_number_seen,
    watchdog_count,
    last_fault_code,
    status_capture_valid
);
input clk;
input rst_n;
input [7:0] mmio_addr;
input [31:0] mmio_wdata;
input mmio_write;
input mmio_valid;
output [31:0] mmio_rdata;
output mmio_ready;
output [15:0] cfg_timeout_limit;
output [1:0] cfg_seq_policy;
output [3:0] cfg_control_mode_permit;
output [7:0] cfg_act_min;
output [7:0] cfg_act_max;
output [7:0] cfg_safe_min;
output [7:0] cfg_safe_max;
output [3:0] cfg_irq_enable;
output cfg_clear_sticky_faults;
output cmd_valid;
output [7:0] cmd_id;
output [15:0] cmd_seq;
output [15:0] cmd_age_ts;
output [3:0] cmd_control_mode;
output [7:0] cmd_act_pos;
output [3:0] cmd_integrity;
input accepted_event;
input rejected_event;
input stale_data_fault;
input timeout_fault;
input clamp_applied;
input fallback_active;
input [15:0] sequence_number_seen;
input [15:0] watchdog_count;
input [7:0] last_fault_code;
input status_capture_valid;

reg [15:0] cfg_timeout_limit_r;
reg [1:0] cfg_seq_policy_r;
reg [3:0] cfg_control_mode_permit_r;
reg [7:0] cfg_act_min_r;
reg [7:0] cfg_act_max_r;
reg [7:0] cfg_safe_min_r;
reg [7:0] cfg_safe_max_r;
reg [3:0] cfg_irq_enable_r;
reg cfg_clear_sticky_faults_r;
reg cmd_valid_r;
reg [7:0] cmd_id_r;
reg [15:0] cmd_seq_r;
reg [15:0] cmd_age_ts_r;
reg [3:0] cmd_control_mode_r;
reg [7:0] cmd_act_pos_r;
reg [3:0] cmd_integrity_r;
reg [31:0] mmio_rdata_r;
reg mmio_ready_r;
reg [31:0] status_shadow;

assign cfg_timeout_limit = cfg_timeout_limit_r;
assign cfg_seq_policy = cfg_seq_policy_r;
assign cfg_control_mode_permit = cfg_control_mode_permit_r;
assign cfg_act_min = cfg_act_min_r;
assign cfg_act_max = cfg_act_max_r;
assign cfg_safe_min = cfg_safe_min_r;
assign cfg_safe_max = cfg_safe_max_r;
assign cfg_irq_enable = cfg_irq_enable_r;
assign cfg_clear_sticky_faults = cfg_clear_sticky_faults_r;
assign cmd_valid = cmd_valid_r;
assign cmd_id = cmd_id_r;
assign cmd_seq = cmd_seq_r;
assign cmd_age_ts = cmd_age_ts_r;
assign cmd_control_mode = cmd_control_mode_r;
assign cmd_act_pos = cmd_act_pos_r;
assign cmd_integrity = cmd_integrity_r;
assign mmio_rdata = mmio_rdata_r;
assign mmio_ready = mmio_ready_r;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_timeout_limit_r <= 16'd1000;
        cfg_seq_policy_r <= 2'b00;
        cfg_control_mode_permit_r <= 4'hF;
        cfg_act_min_r <= 8'h00;
        cfg_act_max_r <= 8'hFF;
        cfg_safe_min_r <= 8'h00;
        cfg_safe_max_r <= 8'hFF;
        cfg_irq_enable_r <= 4'h0;
        cfg_clear_sticky_faults_r <= 1'b0;
        cmd_valid_r <= 1'b0;
        cmd_id_r <= 8'h00;
        cmd_seq_r <= 16'h0000;
        cmd_age_ts_r <= 16'h0000;
        cmd_control_mode_r <= 4'h0;
        cmd_act_pos_r <= 8'h00;
        cmd_integrity_r <= 4'h0;
        mmio_ready_r <= 1'b1;
        status_shadow <= 32'h00000000;
    end else begin
        cfg_clear_sticky_faults_r <= 1'b0;
        if (mmio_valid && mmio_write) begin
            case (mmio_addr)
                8'h00: begin
                    cmd_valid_r <= mmio_wdata[0];
                    cmd_control_mode_r <= mmio_wdata[7:4];
                    cmd_integrity_r <= mmio_wdata[11:8];
                end
                8'h04: begin
                    cmd_id_r <= mmio_wdata[7:0];
                    cmd_seq_r <= mmio_wdata[23:8];
                    cmd_age_ts_r <= mmio_wdata[31:24];
                end
                8'h08: begin
                    cmd_act_pos_r <= mmio_wdata[7:0];
                end
                8'h0C: begin
                    cfg_timeout_limit_r <= mmio_wdata[15:0];
                    cfg_seq_policy_r <= mmio_wdata[17:16];
                    cfg_control_mode_permit_r <= mmio_wdata[21:18];
                end
                8'h10: begin
                    cfg_act_min_r <= mmio_wdata[7:0];
                    cfg_act_max_r <= mmio_wdata[15:8];
                    cfg_safe_min_r <= mmio_wdata[23:16];
                    cfg_safe_max_r <= mmio_wdata[31:24];
                end
                8'h14: begin
                    cfg_irq_enable_r <= mmio_wdata[3:0];
                    cfg_clear_sticky_faults_r <= mmio_wdata[31];
                end
                default: begin
                end
            endcase
        end
        if (status_capture_valid) begin
            status_shadow <= {last_fault_code, sequence_number_seen, fallback_active, clamp_applied, timeout_fault, stale_data_fault, rejected_event, accepted_event, 2'b0};
        end
    end
end

always @(*) begin
    mmio_rdata_r = 32'h00000000;
    case (mmio_addr)
        8'h00: mmio_rdata_r = {20'h00000, cmd_integrity_r, cmd_control_mode_r, 3'b000, cmd_valid_r};
        8'h04: mmio_rdata_r = {cmd_age_ts_r[7:0], cmd_seq_r, cmd_id_r};
        8'h08: mmio_rdata_r = {24'h000000, cmd_act_pos_r};
        8'h0C: mmio_rdata_r = {10'h000, cfg_control_mode_permit_r, cfg_seq_policy_r, cfg_timeout_limit_r};
        8'h10: mmio_rdata_r = {cfg_safe_max_r, cfg_safe_min_r, cfg_act_max_r, cfg_act_min_r};
        8'h14: mmio_rdata_r = {cfg_clear_sticky_faults_r, 27'h0000000, cfg_irq_enable_r};
        8'h18: mmio_rdata_r = {last_fault_code, sequence_number_seen, 2'b00, fallback_active, clamp_applied, timeout_fault, stale_data_fault, rejected_event, accepted_event};
        8'h1C: mmio_rdata_r = {status_capture_valid, 15'h0000, watchdog_count};
        default: mmio_rdata_r = status_shadow;
    endcase
end

endmodule
