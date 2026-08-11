module fallback_fsm (
    input         clk,
    input         reset_n,
    input         enable,
    input         valid_command_seen,
    input         stale_reject,
    input         checksum_fault,
    input         parser_error,
    input         timeout_fault,
    input         clamp_active,
    input         wait_active,
    input  [7:0] last_good_sequence,
    input  [15:0] clamped_command_value,
    input  [3:0] validated_command_mode,
    input  [15:0] fallback_command,
    input         hold_last_good_enable,
    input         freshness_ok,
    output reg [1:0] fallback_state,
    output reg [15:0] final_command_value,
    output reg [3:0] final_command_mode,
    output reg [7:0] safety_flags,
    output reg    fallback_active
);

localparam STATE_NORMAL = 2'd0;
localparam STATE_HOLD   = 2'd1;
localparam STATE_SAFE   = 2'd2;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        fallback_state <= STATE_SAFE;
        final_command_value <= 16'd0;
        final_command_mode <= 4'd0;
        safety_flags <= 8'd0;
        fallback_active <= 1'b1;
    end else begin
        safety_flags <= {3'b000, fallback_active, clamp_active, timeout_fault, checksum_fault, parser_error};
        if (!enable || timeout_fault || checksum_fault || parser_error || stale_reject) begin
            fallback_state <= STATE_SAFE;
            final_command_value <= fallback_command;
            final_command_mode <= 4'd0;
            fallback_active <= 1'b1;
        end else if (valid_command_seen && freshness_ok) begin
            fallback_state <= STATE_NORMAL;
            final_command_value <= clamped_command_value;
            final_command_mode <= validated_command_mode;
            fallback_active <= 1'b0;
        end else if (hold_last_good_enable && wait_active) begin
            fallback_state <= STATE_HOLD;
            final_command_value <= clamped_command_value;
            final_command_mode <= validated_command_mode;
            fallback_active <= 1'b0;
        end else begin
            fallback_state <= STATE_SAFE;
            final_command_value <= fallback_command;
            final_command_mode <= 4'd0;
            fallback_active <= 1'b1;
        end
        safety_flags[7] <= enable;
        safety_flags[6] <= fallback_active;
        safety_flags[5] <= clamp_active;
        safety_flags[4] <= timeout_fault;
        safety_flags[3] <= checksum_fault;
        safety_flags[2] <= parser_error;
        safety_flags[1] <= stale_reject;
        safety_flags[0] <= valid_command_seen;
    end
end

endmodule
