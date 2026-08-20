module adaptive_aero_control_supervisor (
    clk,
    reset,
    cfg_enable,
    cfg_mode_select,
    cfg_request_sequence,
    cfg_timeout_limit,
    cfg_stale_limit,
    cfg_velocity_mps,
    cfg_velocity_min_mps,
    cfg_velocity_max_mps,
    cfg_actuator_min,
    cfg_actuator_max,
    cfg_actuator_safe_pos,
    cfg_interrupt_mask,
    cfg_clear_faults,
    response_accepted,
    response_rejected,
    response_stale,
    response_timeout,
    response_clamp_required,
    response_sequence,
    response_drag_summary,
    response_lift_summary,
    response_recommendation,
    response_metadata,
    accepted_rsp_count,
    rejected_rsp_count,
    stale_event_count,
    timeout_event_count,
    clamp_event_count,
    last_good_sequence,
    last_fault_code,
    fault_status,
    fault_code,
    status_rsp_accepted,
    status_rsp_rejected,
    status_stale_event,
    status_timeout_event,
    status_clamp_event,
    status_safe_inhibit,
    status_fault_latched,
    actuator_cmd_pos,
    actuator_cmd_rate,
    actuator_cmd_valid,
    irq_o
);

input clk;
input reset;
input cfg_enable;
input [2:0] cfg_mode_select;
input [7:0] cfg_request_sequence;
input [15:0] cfg_timeout_limit;
input [7:0] cfg_stale_limit;
input [15:0] cfg_velocity_mps;
input [15:0] cfg_velocity_min_mps;
input [15:0] cfg_velocity_max_mps;
input [15:0] cfg_actuator_min;
input [15:0] cfg_actuator_max;
input [15:0] cfg_actuator_safe_pos;
input [7:0] cfg_interrupt_mask;
input cfg_clear_faults;
input response_accepted;
input response_rejected;
input response_stale;
input response_timeout;
input response_clamp_required;
input [7:0] response_sequence;
input [15:0] response_drag_summary;
input [15:0] response_lift_summary;
input [15:0] response_recommendation;
input [31:0] response_metadata;
output [15:0] accepted_rsp_count;
output [15:0] rejected_rsp_count;
output [15:0] stale_event_count;
output [15:0] timeout_event_count;
output [15:0] clamp_event_count;
output [7:0] last_good_sequence;
output [7:0] last_fault_code;
output [15:0] fault_status;
output [7:0] fault_code;
output status_rsp_accepted;
output status_rsp_rejected;
output status_stale_event;
output status_timeout_event;
output status_clamp_event;
output status_safe_inhibit;
output status_fault_latched;
output [15:0] actuator_cmd_pos;
output [15:0] actuator_cmd_rate;
output actuator_cmd_valid;
output irq_o;

reg [15:0] accepted_rsp_count_r;
reg [15:0] rejected_rsp_count_r;
reg [15:0] stale_event_count_r;
reg [15:0] timeout_event_count_r;
reg [15:0] clamp_event_count_r;
reg [7:0] last_good_sequence_r;
reg [7:0] last_fault_code_r;
reg [15:0] fault_status_r;
reg [7:0] fault_code_r;
reg status_rsp_accepted_r;
reg status_rsp_rejected_r;
reg status_stale_event_r;
reg status_timeout_event_r;
reg status_clamp_event_r;
reg status_safe_inhibit_r;
reg status_fault_latched_r;
reg [15:0] actuator_cmd_pos_r;
reg [15:0] actuator_cmd_rate_r;
reg actuator_cmd_valid_r;
reg irq_o_r;
reg [15:0] watchdog_cnt;
reg [15:0] stale_cnt;
reg [15:0] event_pos;

wire fault_present;
wire safe_inhibit_now;
wire clamp_event_now;
wire accepted_now;
wire rejected_now;
wire stale_now;
wire timeout_now;
wire clear_now;
wire [15:0] clamped_pos;
wire [15:0] clamped_rate;

assign accepted_now = response_accepted;
assign rejected_now = response_rejected;
assign stale_now = response_stale;
assign timeout_now = response_timeout;
assign clamp_event_now = response_clamp_required;
assign clear_now = cfg_clear_faults;
assign fault_present = (fault_status_r != 16'h0000);
assign safe_inhibit_now = (~cfg_enable) | fault_present | stale_now | timeout_now | rejected_now;
assign clamped_pos = (response_recommendation < cfg_actuator_min) ? cfg_actuator_min :
                     (response_recommendation > cfg_actuator_max) ? cfg_actuator_max :
                     response_recommendation;
assign clamped_rate = (response_drag_summary < cfg_actuator_min) ? cfg_actuator_min :
                      (response_drag_summary > cfg_actuator_max) ? cfg_actuator_max :
                      response_drag_summary;

always @(posedge clk) begin
    if (reset) begin
        accepted_rsp_count_r <= 16'h0000;
        rejected_rsp_count_r <= 16'h0000;
        stale_event_count_r <= 16'h0000;
        timeout_event_count_r <= 16'h0000;
        clamp_event_count_r <= 16'h0000;
        last_good_sequence_r <= 8'h00;
        last_fault_code_r <= 8'h00;
        fault_status_r <= 16'h0000;
        fault_code_r <= 8'h00;
        status_rsp_accepted_r <= 1'b0;
        status_rsp_rejected_r <= 1'b0;
        status_stale_event_r <= 1'b0;
        status_timeout_event_r <= 1'b0;
        status_clamp_event_r <= 1'b0;
        status_safe_inhibit_r <= 1'b1;
        status_fault_latched_r <= 1'b0;
        actuator_cmd_pos_r <= 16'h0000;
        actuator_cmd_rate_r <= 16'h0000;
        actuator_cmd_valid_r <= 1'b0;
        irq_o_r <= 1'b0;
        watchdog_cnt <= 16'h0000;
        stale_cnt <= 16'h0000;
        event_pos <= 16'h0000;
    end else begin
        status_rsp_accepted_r <= 1'b0;
        status_rsp_rejected_r <= 1'b0;
        status_stale_event_r <= 1'b0;
        status_timeout_event_r <= 1'b0;
        status_clamp_event_r <= 1'b0;
        status_safe_inhibit_r <= safe_inhibit_now;
        status_fault_latched_r <= (fault_status_r != 16'h0000);

        if (clear_now) begin
            fault_status_r <= 16'h0000;
            fault_code_r <= 8'h00;
        end

        watchdog_cnt <= watchdog_cnt + 16'h0001;
        stale_cnt <= stale_cnt + 16'h0001;
        event_pos <= event_pos + 16'h0001;

        if (accepted_now) begin
            accepted_rsp_count_r <= accepted_rsp_count_r + 16'h0001;
            last_good_sequence_r <= response_sequence;
            status_rsp_accepted_r <= 1'b1;
            actuator_cmd_pos_r <= clamped_pos;
            actuator_cmd_rate_r <= clamped_rate;
            actuator_cmd_valid_r <= cfg_enable & ~fault_present;
            watchdog_cnt <= 16'h0000;
            stale_cnt <= 16'h0000;
        end else begin
            actuator_cmd_valid_r <= 1'b0;
        end

        if (rejected_now) begin
            rejected_rsp_count_r <= rejected_rsp_count_r + 16'h0001;
            status_rsp_rejected_r <= 1'b1;
            fault_status_r[0] <= 1'b1;
            fault_code_r <= 8'h01;
            last_fault_code_r <= 8'h01;
        end
        if (stale_now) begin
            stale_event_count_r <= stale_event_count_r + 16'h0001;
            status_stale_event_r <= 1'b1;
            fault_status_r[1] <= 1'b1;
            fault_code_r <= 8'h02;
            last_fault_code_r <= 8'h02;
        end
        if (timeout_now || (watchdog_cnt >= cfg_timeout_limit)) begin
            timeout_event_count_r <= timeout_event_count_r + 16'h0001;
            status_timeout_event_r <= 1'b1;
            fault_status_r[2] <= 1'b1;
            fault_code_r <= 8'h03;
            last_fault_code_r <= 8'h03;
            watchdog_cnt <= 16'h0000;
        end
        if (clamp_event_now || (response_recommendation < cfg_actuator_min) || (response_recommendation > cfg_actuator_max) || (response_drag_summary < cfg_actuator_min) || (response_drag_summary > cfg_actuator_max)) begin
            clamp_event_count_r <= clamp_event_count_r + 16'h0001;
            status_clamp_event_r <= 1'b1;
            fault_status_r[3] <= 1'b1;
            fault_code_r <= 8'h04;
            last_fault_code_r <= 8'h04;
        end

        if (safe_inhibit_now) begin
            status_safe_inhibit_r <= 1'b1;
            actuator_cmd_valid_r <= 1'b0;
        end

        irq_o_r <= ((cfg_interrupt_mask[0] & accepted_now) |
                    (cfg_interrupt_mask[1] & rejected_now) |
                    (cfg_interrupt_mask[2] & stale_now) |
                    (cfg_interrupt_mask[3] & timeout_now) |
                    (cfg_interrupt_mask[4] & clamp_event_now) |
                    (cfg_interrupt_mask[5] & (fault_status_r != 16'h0000)));
    end
end

assign accepted_rsp_count = accepted_rsp_count_r;
assign rejected_rsp_count = rejected_rsp_count_r;
assign stale_event_count = stale_event_count_r;
assign timeout_event_count = timeout_event_count_r;
assign clamp_event_count = clamp_event_count_r;
assign last_good_sequence = last_good_sequence_r;
assign last_fault_code = last_fault_code_r;
assign fault_status = fault_status_r;
assign fault_code = fault_code_r;
assign status_rsp_accepted = status_rsp_accepted_r;
assign status_rsp_rejected = status_rsp_rejected_r;
assign status_stale_event = status_stale_event_r;
assign status_timeout_event = status_timeout_event_r;
assign status_clamp_event = status_clamp_event_r;
assign status_safe_inhibit = status_safe_inhibit_r;
assign status_fault_latched = status_fault_latched_r;
assign actuator_cmd_pos = actuator_cmd_pos_r;
assign actuator_cmd_rate = actuator_cmd_rate_r;
assign actuator_cmd_valid = actuator_cmd_valid_r;
assign irq_o = irq_o_r;

endmodule
