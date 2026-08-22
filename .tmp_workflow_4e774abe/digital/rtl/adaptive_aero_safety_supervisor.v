module adaptive_aero_safety_supervisor (
    clk,
    rst_n,
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
    status_capture_valid,
    actuator_cmd_out,
    host_irq
);
input clk;
input rst_n;
input [15:0] cfg_timeout_limit;
input [1:0] cfg_seq_policy;
input [3:0] cfg_control_mode_permit;
input [7:0] cfg_act_min;
input [7:0] cfg_act_max;
input [7:0] cfg_safe_min;
input [7:0] cfg_safe_max;
input [3:0] cfg_irq_enable;
input cfg_clear_sticky_faults;
input cmd_valid;
input [7:0] cmd_id;
input [15:0] cmd_seq;
input [15:0] cmd_age_ts;
input [3:0] cmd_control_mode;
input [7:0] cmd_act_pos;
input [3:0] cmd_integrity;
output accepted_event;
output rejected_event;
output stale_data_fault;
output timeout_fault;
output clamp_applied;
output fallback_active;
output [15:0] sequence_number_seen;
output [15:0] watchdog_count;
output [7:0] last_fault_code;
output status_capture_valid;
output [31:0] actuator_cmd_out;
output host_irq;

reg accepted_event_r;
reg rejected_event_r;
reg stale_data_fault_r;
reg timeout_fault_r;
reg clamp_applied_r;
reg fallback_active_r;
reg [15:0] sequence_number_seen_r;
reg [15:0] watchdog_count_r;
reg [7:0] last_fault_code_r;
reg status_capture_valid_r;
reg [31:0] actuator_cmd_out_r;
reg host_irq_r;
reg [15:0] last_seq_r;
reg [7:0] last_cmd_id_r;
reg [7:0] latched_act_r;
reg [3:0] latched_mode_r;
reg sticky_fault_r;
reg [15:0] timeout_limit_eff;
reg [7:0] act_min_eff;
reg [7:0] act_max_eff;
reg [7:0] safe_min_eff;
reg [7:0] safe_max_eff;
reg [7:0] clamped_act;
reg [7:0] raw_act;
reg valid_seq;
reg valid_mode;
reg valid_age;
reg valid_range;
reg seq_ok;
reg new_accept;
reg [15:0] watchdog_next;
reg timeout_now;
reg [7:0] fault_code_next;
reg irq_event;

assign accepted_event = accepted_event_r;
assign rejected_event = rejected_event_r;
assign stale_data_fault = stale_data_fault_r;
assign timeout_fault = timeout_fault_r;
assign clamp_applied = clamp_applied_r;
assign fallback_active = fallback_active_r;
assign sequence_number_seen = sequence_number_seen_r;
assign watchdog_count = watchdog_count_r;
assign last_fault_code = last_fault_code_r;
assign status_capture_valid = status_capture_valid_r;
assign actuator_cmd_out = actuator_cmd_out_r;
assign host_irq = host_irq_r;

always @(*) begin
    timeout_limit_eff = cfg_timeout_limit;
    act_min_eff = cfg_act_min;
    act_max_eff = cfg_act_max;
    safe_min_eff = cfg_safe_min;
    safe_max_eff = cfg_safe_max;
    raw_act = cmd_act_pos;
    clamped_act = raw_act;
    if (act_min_eff > act_max_eff)
        clamped_act = act_min_eff;
    else if (raw_act < act_min_eff)
        clamped_act = act_min_eff;
    else if (raw_act > act_max_eff)
        clamped_act = act_max_eff;
    valid_mode = ((cfg_control_mode_permit & cmd_control_mode) != 4'h0);
    valid_seq = 1'b0;
    case (cfg_seq_policy)
        2'b00: valid_seq = 1'b1;
        2'b01: valid_seq = (cmd_seq != last_seq_r);
        2'b10: valid_seq = (cmd_seq > last_seq_r);
        2'b11: valid_seq = (cmd_seq != last_seq_r);
        default: valid_seq = 1'b0;
    endcase
    valid_age = 1'b1;
    if (cfg_timeout_limit != 16'h0000)
        valid_age = (cmd_age_ts <= cfg_timeout_limit);
    valid_range = (cmd_act_pos >= safe_min_eff) && (cmd_act_pos <= safe_max_eff);
    seq_ok = valid_seq;
    new_accept = cmd_valid && valid_mode && valid_seq && valid_age && valid_range;
    timeout_now = 1'b0;
    if (cfg_timeout_limit != 16'h0000)
        timeout_now = (watchdog_count_r >= cfg_timeout_limit);
    watchdog_next = watchdog_count_r;
    if (new_accept)
        watchdog_next = 16'h0000;
    else if (!timeout_now)
        watchdog_next = watchdog_count_r + 16'h0001;
    irq_event = 1'b0;
    if (new_accept && ((cfg_irq_enable[0]) != 1'b0))
        irq_event = 1'b1;
    if ((!new_accept) && cmd_valid && ((cfg_irq_enable[1]) != 1'b0))
        irq_event = 1'b1;
    if (timeout_now && ((cfg_irq_enable[3]) != 1'b0))
        irq_event = 1'b1;
    if (stale_data_fault_r && ((cfg_irq_enable[2]) != 1'b0))
        irq_event = 1'b1;
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        accepted_event_r <= 1'b0;
        rejected_event_r <= 1'b0;
        stale_data_fault_r <= 1'b0;
        timeout_fault_r <= 1'b0;
        clamp_applied_r <= 1'b0;
        fallback_active_r <= 1'b1;
        sequence_number_seen_r <= 16'h0000;
        watchdog_count_r <= 16'h0000;
        last_fault_code_r <= 8'h00;
        status_capture_valid_r <= 1'b0;
        actuator_cmd_out_r <= 32'h00000000;
        host_irq_r <= 1'b0;
        last_seq_r <= 16'h0000;
        last_cmd_id_r <= 8'h00;
        latched_act_r <= 8'h00;
        latched_mode_r <= 4'h0;
        sticky_fault_r <= 1'b0;
    end else begin
        accepted_event_r <= 1'b0;
        rejected_event_r <= 1'b0;
        status_capture_valid_r <= 1'b0;
        if (cfg_clear_sticky_faults) begin
            stale_data_fault_r <= 1'b0;
            timeout_fault_r <= 1'b0;
            sticky_fault_r <= 1'b0;
            last_fault_code_r <= 8'h00;
        end
        if (new_accept) begin
            accepted_event_r <= 1'b1;
            fallback_active_r <= 1'b0;
            sequence_number_seen_r <= cmd_seq;
            last_seq_r <= cmd_seq;
            last_cmd_id_r <= cmd_id;
            latched_act_r <= clamped_act;
            latched_mode_r <= cmd_control_mode;
            clamp_applied_r <= (clamped_act != cmd_act_pos);
            actuator_cmd_out_r <= {24'h000000, clamped_act};
            watchdog_count_r <= 16'h0000;
            status_capture_valid_r <= 1'b1;
            last_fault_code_r <= 8'h00;
        end else begin
            if (cmd_valid) begin
                rejected_event_r <= 1'b1;
                sticky_fault_r <= 1'b1;
                if (!valid_mode)
                    last_fault_code_r <= 8'h11;
                else if (!valid_seq)
                    last_fault_code_r <= 8'h21;
                else if (!valid_age)
                    last_fault_code_r <= 8'h31;
                else if (!valid_range)
                    last_fault_code_r <= 8'h41;
                else
                    last_fault_code_r <= 8'h51;
            end
            if (timeout_now) begin
                timeout_fault_r <= 1'b1;
                stale_data_fault_r <= 1'b1;
                sticky_fault_r <= 1'b1;
                fallback_active_r <= 1'b1;
                actuator_cmd_out_r <= 32'h00000000;
                last_fault_code_r <= 8'h80;
                status_capture_valid_r <= 1'b1;
            end
            watchdog_count_r <= watchdog_next;
            if (watchdog_next == 16'h0000)
                fallback_active_r <= 1'b0;
        end
        if (cfg_clear_sticky_faults) begin
            status_capture_valid_r <= 1'b1;
        end
        if (sticky_fault_r || stale_data_fault_r || timeout_fault_r)
            host_irq_r <= irq_event;
        else
            host_irq_r <= irq_event;
        if (!new_accept && !cmd_valid && !timeout_now) begin
            if (act_min_eff > act_max_eff) begin
                actuator_cmd_out_r <= {24'h000000, act_min_eff};
                clamp_applied_r <= 1'b1;
            end
        end
        if (stale_data_fault_r || timeout_fault_r || sticky_fault_r) begin
            fallback_active_r <= 1'b1;
        end
    end
end

endmodule
