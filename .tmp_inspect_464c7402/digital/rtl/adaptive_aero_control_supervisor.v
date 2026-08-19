module adaptive_aero_control_supervisor (
    clk,
    rst_n,
    ctrl_enable,
    ctrl_clear_fault,
    ctrl_arm_output,
    ctrl_bypass_model,
    timeout_cfg_cycles,
    stale_cfg_cycles,
    cmd_min,
    cmd_max,
    cmd_safe,
    seq_tx,
    seq_rx,
    rsp_seq_rx,
    rsp_status,
    rsp_cmd_suggest,
    rsp_quality,
    rsp_age_echo,
    meta_velocity_bucket,
    meta_mode,
    meta_env_flags,
    meta_session_id,
    status_busy,
    status_req_pending,
    status_rsp_seen,
    status_stale_fault,
    status_timeout_fault,
    status_range_fault,
    status_fallback_active,
    status_last_good_valid,
    actuator_cmd,
    actuator_cmd_valid,
    fault_status
);

input clk;
input rst_n;
input ctrl_enable;
input ctrl_clear_fault;
input ctrl_arm_output;
input ctrl_bypass_model;
input [31:0] timeout_cfg_cycles;
input [31:0] stale_cfg_cycles;
input [15:0] cmd_min;
input [15:0] cmd_max;
input [15:0] cmd_safe;
input [15:0] seq_tx;
output [15:0] seq_rx;
input [15:0] rsp_seq_rx;
input [7:0] rsp_status;
input [15:0] rsp_cmd_suggest;
input [7:0] rsp_quality;
input [15:0] rsp_age_echo;
input [7:0] meta_velocity_bucket;
input [3:0] meta_mode;
input [3:0] meta_env_flags;
input [15:0] meta_session_id;
output status_busy;
output status_req_pending;
output status_rsp_seen;
output status_stale_fault;
output status_timeout_fault;
output status_range_fault;
output status_fallback_active;
output status_last_good_valid;
output [15:0] actuator_cmd;
output actuator_cmd_valid;
output [7:0] fault_status;
reg [15:0] seq_rx_r;
reg status_busy_r;
reg status_req_pending_r;
reg status_rsp_seen_r;
reg status_stale_fault_r;
reg status_timeout_fault_r;
reg status_range_fault_r;
reg status_fallback_active_r;
reg status_last_good_valid_r;
reg [15:0] actuator_cmd_r;
reg actuator_cmd_valid_r;
reg [7:0] fault_status_r;
reg [15:0] last_good_cmd;
reg [15:0] watchdog_count;
reg [15:0] stale_count;
reg [15:0] expected_seq;
reg pending_req;
reg fault_latched;
reg [15:0] clamped_cmd;
reg rsp_good;
wire seq_match;
wire meta_ok;
wire cmd_in_range;
wire [15:0] min_cmd;
wire [15:0] max_cmd;
wire [15:0] suggested_cmd;
assign seq_match = (rsp_seq_rx == seq_tx);
assign meta_ok = (meta_velocity_bucket >= 8'd20) & (meta_velocity_bucket <= 8'd55);
assign min_cmd = cmd_min;
assign max_cmd = cmd_max;
assign suggested_cmd = rsp_cmd_suggest;
assign cmd_in_range = (suggested_cmd >= min_cmd) & (suggested_cmd <= max_cmd);

assign seq_rx = seq_rx_r;
assign status_busy = status_busy_r;
assign status_req_pending = status_req_pending_r;
assign status_rsp_seen = status_rsp_seen_r;
assign status_stale_fault = status_stale_fault_r;
assign status_timeout_fault = status_timeout_fault_r;
assign status_range_fault = status_range_fault_r;
assign status_fallback_active = status_fallback_active_r;
assign status_last_good_valid = status_last_good_valid_r;
assign actuator_cmd = actuator_cmd_r;
assign actuator_cmd_valid = actuator_cmd_valid_r;
assign fault_status = fault_status_r;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        seq_rx_r <= 16'h0000;
        status_busy_r <= 1'b0;
        status_req_pending_r <= 1'b0;
        status_rsp_seen_r <= 1'b0;
        status_stale_fault_r <= 1'b0;
        status_timeout_fault_r <= 1'b0;
        status_range_fault_r <= 1'b0;
        status_fallback_active_r <= 1'b1;
        status_last_good_valid_r <= 1'b0;
        actuator_cmd_r <= 16'h0000;
        actuator_cmd_valid_r <= 1'b0;
        fault_status_r <= 8'h00;
        last_good_cmd <= 16'h0000;
        watchdog_count <= 16'h0000;
        stale_count <= 16'h0000;
        expected_seq <= 16'h0000;
        pending_req <= 1'b0;
        fault_latched <= 1'b0;
        clamped_cmd <= 16'h0000;
        rsp_good <= 1'b0;
    end else begin
        status_rsp_seen_r <= 1'b0;
        if (ctrl_clear_fault) begin
            status_stale_fault_r <= 1'b0;
            status_timeout_fault_r <= 1'b0;
            status_range_fault_r <= 1'b0;
            fault_latched <= 1'b0;
        end
        status_busy_r <= ctrl_enable & (pending_req | status_req_pending_r);
        status_req_pending_r <= ctrl_enable & ctrl_arm_output & ~fault_latched;
        status_fallback_active_r <= (~ctrl_enable) | (~ctrl_arm_output) | fault_latched | status_stale_fault_r | status_timeout_fault_r | status_range_fault_r;
        status_last_good_valid_r <= status_last_good_valid_r & ~(~ctrl_enable | fault_latched);
        if (ctrl_enable & ctrl_arm_output & ~fault_latched) begin
            pending_req <= 1'b1;
            expected_seq <= seq_tx;
            watchdog_count <= watchdog_count + 16'h0001;
            stale_count <= stale_count + 16'h0001;
        end else begin
            pending_req <= 1'b0;
            watchdog_count <= 16'h0000;
            stale_count <= 16'h0000;
            actuator_cmd_valid_r <= 1'b0;
        end
        if (rsp_seq_rx == expected_seq) begin
            seq_rx_r <= rsp_seq_rx;
            status_rsp_seen_r <= 1'b1;
            rsp_good <= (rsp_status[0] == 1'b0) & meta_ok;
            if ((rsp_status[0] == 1'b0) & meta_ok & ~fault_latched & ctrl_enable & ctrl_arm_output) begin
                if (suggested_cmd < min_cmd) begin
                    clamped_cmd <= min_cmd;
                    status_range_fault_r <= 1'b1;
                    fault_latched <= 1'b1;
                    fault_status_r[5] <= 1'b1;
                end else if (suggested_cmd > max_cmd) begin
                    clamped_cmd <= max_cmd;
                    status_range_fault_r <= 1'b1;
                    fault_latched <= 1'b1;
                    fault_status_r[5] <= 1'b1;
                end else begin
                    clamped_cmd <= suggested_cmd;
                end
                if (~status_range_fault_r) begin
                    actuator_cmd_r <= (suggested_cmd < min_cmd) ? min_cmd : ((suggested_cmd > max_cmd) ? max_cmd : suggested_cmd);
                    actuator_cmd_valid_r <= 1'b1;
                    last_good_cmd <= (suggested_cmd < min_cmd) ? min_cmd : ((suggested_cmd > max_cmd) ? max_cmd : suggested_cmd);
                    status_last_good_valid_r <= 1'b1;
                end
            end else begin
                actuator_cmd_valid_r <= 1'b0;
                fault_latched <= 1'b1;
            end
        end else if (pending_req) begin
            if (watchdog_count >= timeout_cfg_cycles[15:0]) begin
                status_timeout_fault_r <= 1'b1;
                fault_latched <= 1'b1;
                actuator_cmd_valid_r <= 1'b0;
            end
            if (stale_count >= stale_cfg_cycles[15:0]) begin
                status_stale_fault_r <= 1'b1;
                fault_latched <= 1'b1;
                actuator_cmd_valid_r <= 1'b0;
            end
        end else begin
            actuator_cmd_valid_r <= 1'b0;
        end
        fault_status_r[0] <= fault_latched;
        fault_status_r[1] <= status_timeout_fault_r;
        fault_status_r[2] <= status_stale_fault_r;
        fault_status_r[3] <= status_range_fault_r;
        fault_status_r[4] <= pending_req;
        fault_status_r[5] <= status_last_good_valid_r;
        fault_status_r[6] <= ctrl_enable;
        fault_status_r[7] <= ctrl_arm_output;
    end
end

endmodule
