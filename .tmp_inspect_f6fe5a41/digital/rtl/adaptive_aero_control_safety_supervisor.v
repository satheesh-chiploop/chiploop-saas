module adaptive_aero_control_safety_supervisor (
    clk,
    reset_n,
    cfg_enable_i,
    cfg_arm_i,
    cfg_timeout_threshold_i,
    cfg_sequence_counter_i,
    cfg_fault_clear_w1c_i,
    response_valid_i,
    response_sequence_i,
    response_fresh_i,
    response_status_flags_i,
    local_timestamp_i,
    last_seen_sequence_o,
    fresh_o,
    stale_o,
    timeout_o,
    fault_sticky_o,
    irq_event_o,
    allow_command_o
);
input clk;
input reset_n;
input cfg_enable_i;
input cfg_arm_i;
input [15:0] cfg_timeout_threshold_i;
input [15:0] cfg_sequence_counter_i;
input [7:0] cfg_fault_clear_w1c_i;
input response_valid_i;
input [15:0] response_sequence_i;
input response_fresh_i;
input [7:0] response_status_flags_i;
input [31:0] local_timestamp_i;
output [15:0] last_seen_sequence_o;
output fresh_o;
output stale_o;
output timeout_o;
output [7:0] fault_sticky_o;
output irq_event_o;
output allow_command_o;

reg [15:0] last_seen_sequence_r;
reg fresh_r;
reg stale_r;
reg timeout_r;
reg [7:0] fault_sticky_r;
reg irq_event_r;
reg allow_command_r;
reg [31:0] last_timestamp_r;

assign last_seen_sequence_o = last_seen_sequence_r;
assign fresh_o = fresh_r;
assign stale_o = stale_r;
assign timeout_o = timeout_r;
assign fault_sticky_o = fault_sticky_r;
assign irq_event_o = irq_event_r;
assign allow_command_o = allow_command_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        last_seen_sequence_r <= 16'h0000;
        fresh_r <= 1'b0;
        stale_r <= 1'b0;
        timeout_r <= 1'b0;
        fault_sticky_r <= 8'h00;
        irq_event_r <= 1'b0;
        allow_command_r <= 1'b0;
        last_timestamp_r <= 32'h00000000;
    end else begin
        irq_event_r <= 1'b0;
        fresh_r <= 1'b0;
        stale_r <= 1'b0;
        timeout_r <= 1'b0;
        if (cfg_fault_clear_w1c_i[0]) fault_sticky_r[0] <= 1'b0;
        if (cfg_fault_clear_w1c_i[1]) fault_sticky_r[1] <= 1'b0;
        if (cfg_fault_clear_w1c_i[2]) fault_sticky_r[2] <= 1'b0;
        if (cfg_fault_clear_w1c_i[3]) fault_sticky_r[3] <= 1'b0;
        if (cfg_fault_clear_w1c_i[4]) fault_sticky_r[4] <= 1'b0;
        if (cfg_fault_clear_w1c_i[5]) fault_sticky_r[5] <= 1'b0;
        if (cfg_fault_clear_w1c_i[6]) fault_sticky_r[6] <= 1'b0;
        if (cfg_fault_clear_w1c_i[7]) fault_sticky_r[7] <= 1'b0;
        if (response_valid_i) begin
            last_seen_sequence_r <= response_sequence_i;
            fresh_r <= response_fresh_i;
            last_timestamp_r <= local_timestamp_i;
            allow_command_r <= cfg_enable_i & cfg_arm_i & response_fresh_i & ~response_status_flags_i[0];
            if (!response_fresh_i) begin
                stale_r <= 1'b1;
                fault_sticky_r[1] <= 1'b1;
                irq_event_r <= 1'b1;
            end else begin
                irq_event_r <= 1'b1;
            end
            if (response_status_flags_i[0]) begin
                fault_sticky_r[0] <= 1'b1;
                irq_event_r <= 1'b1;
            end
            if (response_sequence_i != cfg_sequence_counter_i) begin
                fault_sticky_r[2] <= 1'b1;
                stale_r <= 1'b1;
                irq_event_r <= 1'b1;
            end
        end
        if ((cfg_timeout_threshold_i != 16'h0000) && ((local_timestamp_i - last_timestamp_r) > {16'h0000, cfg_timeout_threshold_i})) begin
            timeout_r <= 1'b1;
            fault_sticky_r[3] <= 1'b1;
            allow_command_r <= 1'b0;
            irq_event_r <= 1'b1;
        end
        if (fault_sticky_r != 8'h00) begin
            allow_command_r <= 1'b0;
        end
        if (!cfg_enable_i || !cfg_arm_i) begin
            allow_command_r <= 1'b0;
        end
    end
end
endmodule
