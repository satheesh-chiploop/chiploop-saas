module adaptive_aero_control_core (
    clk,
    rst_n,
    reg_control_enable,
    reg_control_clear_faults,
    reg_control_arm_safe_fallback,
    reg_control_bypass_output_hold,
    reg_control_mode,
    reg_seq_in,
    reg_age_limit,
    reg_velocity_mps,
    reg_act_min,
    reg_act_max,
    reg_act_cmd,
    reg_irq_ack,
    status_busy,
    status_command_accepted,
    status_stale_rejected,
    status_timeout_fault,
    status_invalid_input,
    status_clamp_applied,
    status_safe_fallback_active,
    status_irq_pending,
    reg_last_good,
    reg_timeout_cnt,
    reg_fault_cause,
    actuator_cmd,
    actuator_valid,
    actuator_ready,
    irq
);

input clk;
input rst_n;
input reg_control_enable;
input reg_control_clear_faults;
input reg_control_arm_safe_fallback;
input reg_control_bypass_output_hold;
input [3:0] reg_control_mode;
input [31:0] reg_seq_in;
input [31:0] reg_age_limit;
input [31:0] reg_velocity_mps;
input [31:0] reg_act_min;
input [31:0] reg_act_max;
input [31:0] reg_act_cmd;
input reg_irq_ack;

output reg status_busy;
output reg status_command_accepted;
output reg status_stale_rejected;
output reg status_timeout_fault;
output reg status_invalid_input;
output reg status_clamp_applied;
output reg status_safe_fallback_active;
output reg status_irq_pending;
output reg [31:0] reg_last_good;
output reg [31:0] reg_timeout_cnt;
output reg [31:0] reg_fault_cause;
output reg [31:0] actuator_cmd;
output reg actuator_valid;
input actuator_ready;
output reg irq;

localparam S_IDLE = 3'd0;
localparam S_VALIDATE = 3'd1;
localparam S_CLAMP = 3'd2;
localparam S_ISSUE = 3'd3;
localparam S_FALLBACK = 3'd4;
localparam S_HOLD = 3'd5;

localparam [31:0] FAULT_STALE = 32'h00000001;
localparam [31:0] FAULT_TIMEOUT = 32'h00000002;
localparam [31:0] FAULT_INVALID = 32'h00000004;
localparam [31:0] FAULT_CLAMP = 32'h00000008;
localparam [31:0] FAULT_FALLBACK = 32'h00000010;

reg [2:0] state;
reg [31:0] last_seq;
reg [31:0] pending_cmd;
reg [31:0] clamped_cmd;
reg [31:0] safe_cmd;
reg [31:0] next_fault_cause;
reg [31:0] next_timeout_cnt;
reg [31:0] field_min;
reg [31:0] field_max;
reg [31:0] field_in;
reg [31:0] field_out;
reg [31:0] tmp_cmd;
reg [31:0] current_cmd;
reg accept_valid;
reg accept_stale;
reg accept_timeout;
reg accept_invalid;
reg accept_clamp;
reg accept_fallback;
reg clear_all_faults;
reg seq_newer;
reg age_valid;
reg vel_valid;
reg [31:0] age_limit_eff;
reg [31:0] velocity_eff;
reg [31:0] timeout_next;
reg [31:0] last_good_next;
reg [31:0] fault_next;
reg busy_next;
reg irq_next;
reg valid_next;
reg [31:0] cmd_next;
reg [31:0] safe_cmd_next;
reg [31:0] clamped_next;
reg [31:0] pending_next;
reg [31:0] last_seq_next;
reg [2:0] state_next;
reg [31:0] count_work;
reg [31:0] mask_work;
integer i;

always @(*) begin
    state_next = state;
    busy_next = status_busy;
    irq_next = irq;
    valid_next = 1'b0;
    cmd_next = actuator_cmd;
    fault_next = reg_fault_cause;
    last_good_next = reg_last_good;
    timeout_next = reg_timeout_cnt;
    safe_cmd_next = safe_cmd;
    clamped_next = clamped_cmd;
    pending_next = pending_cmd;
    last_seq_next = last_seq;
    accept_valid = 1'b0;
    accept_stale = 1'b0;
    accept_timeout = 1'b0;
    accept_invalid = 1'b0;
    accept_clamp = 1'b0;
    accept_fallback = 1'b0;
    clear_all_faults = reg_control_clear_faults;
    seq_newer = 1'b0;
    age_valid = 1'b0;
    vel_valid = 1'b0;
    age_limit_eff = reg_age_limit;
    velocity_eff = reg_velocity_mps;
    field_min = reg_act_min;
    field_max = reg_act_max;
    field_in = reg_act_cmd;
    field_out = reg_act_cmd;
    tmp_cmd = reg_act_cmd;
    current_cmd = actuator_cmd;
    count_work = 32'h00000000;
    mask_work = 32'h00000000;

    if (clear_all_faults) begin
        fault_next = 32'h00000000;
        irq_next = 1'b0;
    end

    if (reg_control_enable) begin
        seq_newer = (reg_seq_in != last_seq) & ((reg_seq_in > last_seq) | (last_seq == 32'h00000000));
        age_valid = (reg_age_limit == 32'h00000000) ? 1'b1 : (reg_timeout_cnt <= reg_age_limit);
        vel_valid = ((reg_velocity_mps >= 32'd20) && (reg_velocity_mps <= 32'd55));

        if (!seq_newer) begin
            accept_stale = 1'b1;
            fault_next = fault_next | FAULT_STALE;
            irq_next = 1'b1;
            state_next = S_HOLD;
        end else if (!age_valid) begin
            accept_timeout = 1'b1;
            fault_next = fault_next | FAULT_TIMEOUT;
            irq_next = 1'b1;
            state_next = S_FALLBACK;
            safe_cmd_next = safe_cmd;
        end else if (!vel_valid) begin
            accept_invalid = 1'b1;
            fault_next = fault_next | FAULT_INVALID | FAULT_FALLBACK;
            irq_next = 1'b1;
            state_next = S_FALLBACK;
            safe_cmd_next = safe_cmd;
        end else begin
            pending_next = reg_act_cmd;
            tmp_cmd = reg_act_cmd;

            if (tmp_cmd < reg_act_min) begin
                tmp_cmd = reg_act_min;
                accept_clamp = 1'b1;
            end
            if (tmp_cmd > reg_act_max) begin
                tmp_cmd = reg_act_max;
                accept_clamp = 1'b1;
            end

            clamped_next = tmp_cmd;
            accept_valid = 1'b1;
            fault_next = fault_next | (accept_clamp ? FAULT_CLAMP : 32'h00000000);
            irq_next = 1'b1;
            last_seq_next = reg_seq_in;
            last_good_next = tmp_cmd;
            safe_cmd_next = reg_control_arm_safe_fallback ? safe_cmd : safe_cmd;
            state_next = (actuator_ready || reg_control_bypass_output_hold) ? S_ISSUE : S_HOLD;
            cmd_next = tmp_cmd;
            valid_next = 1'b1;
        end
    end else begin
        state_next = S_FALLBACK;
        fault_next = fault_next | FAULT_FALLBACK;
        irq_next = irq | reg_control_arm_safe_fallback;
    end

    if (reg_control_arm_safe_fallback) begin
        safe_cmd_next = safe_cmd;
    end

    if (reg_irq_ack) begin
        irq_next = 1'b0;
    end

    if (state == S_FALLBACK) begin
        cmd_next = safe_cmd_next;
        valid_next = 1'b1;
        busy_next = 1'b1;
        fault_next = fault_next | FAULT_FALLBACK;
        accept_fallback = 1'b1;
    end

    if (state == S_ISSUE) begin
        cmd_next = clamped_cmd;
        valid_next = 1'b1;
        busy_next = ~actuator_ready;
        if (actuator_ready) begin
            state_next = S_IDLE;
        end else begin
            state_next = S_HOLD;
        end
    end

    if (state == S_HOLD) begin
        valid_next = 1'b1;
        busy_next = 1'b1;
        cmd_next = actuator_cmd;
        if (actuator_ready && reg_control_enable && !reg_control_bypass_output_hold) begin
            state_next = S_IDLE;
        end
    end

    if (state == S_IDLE) begin
        busy_next = 1'b0;
        if (reg_control_enable) begin
            state_next = S_VALIDATE;
        end
    end

    if (state == S_VALIDATE) begin
        busy_next = 1'b1;
        state_next = S_CLAMP;
    end

    if (state == S_CLAMP) begin
        busy_next = 1'b1;
        state_next = S_ISSUE;
    end

end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= S_FALLBACK;
        last_seq <= 32'h00000000;
        pending_cmd <= 32'h00000000;
        clamped_cmd <= 32'h00000000;
        safe_cmd <= 32'h00000000;
        reg_last_good <= 32'h00000000;
        reg_timeout_cnt <= 32'h00000000;
        reg_fault_cause <= 32'h00000000;
        status_busy <= 1'b0;
        status_command_accepted <= 1'b0;
        status_stale_rejected <= 1'b0;
        status_timeout_fault <= 1'b0;
        status_invalid_input <= 1'b0;
        status_clamp_applied <= 1'b0;
        status_safe_fallback_active <= 1'b1;
        status_irq_pending <= 1'b0;
        actuator_cmd <= 32'h00000000;
        actuator_valid <= 1'b0;
        irq <= 1'b0;
    end else begin
        state <= state_next;
        last_seq <= last_seq_next;
        pending_cmd <= pending_next;
        clamped_cmd <= clamped_next;
        safe_cmd <= safe_cmd_next;
        reg_last_good <= last_good_next;
        reg_timeout_cnt <= timeout_next + 32'd1;
        reg_fault_cause <= fault_next;
        status_busy <= busy_next;
        status_command_accepted <= accept_valid;
        status_stale_rejected <= accept_stale;
        status_timeout_fault <= accept_timeout;
        status_invalid_input <= accept_invalid;
        status_clamp_applied <= accept_clamp;
        status_safe_fallback_active <= (state_next == S_FALLBACK) | accept_timeout | accept_invalid | reg_control_arm_safe_fallback | (~reg_control_enable);
        status_irq_pending <= irq_next;
        actuator_cmd <= cmd_next;
        actuator_valid <= valid_next;
        irq <= irq_next;
    end
end

endmodule
