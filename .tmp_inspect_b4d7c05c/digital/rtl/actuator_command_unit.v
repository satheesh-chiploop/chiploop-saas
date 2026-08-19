module actuator_command_unit (
    clk,
    reset_n,
    actuator_enable,
    allow_command_update,
    drag_estimate,
    lift_estimate,
    confidence_flags,
    actuator_min,
    actuator_max,
    rate_limit,
    safe_mode_select,
    actuator_valid,
    actuator_command,
    last_good_command
);
    input clk;
    input reset_n;
    input actuator_enable;
    input allow_command_update;
    input [31:0] drag_estimate;
    input [31:0] lift_estimate;
    input [7:0] confidence_flags;
    input [31:0] actuator_min;
    input [31:0] actuator_max;
    input [31:0] rate_limit;
    input safe_mode_select;
    output actuator_valid;
    output [31:0] actuator_command;
    output [31:0] last_good_command;
    reg actuator_valid_r;
    reg [31:0] actuator_command_r;
    reg [31:0] last_good_command_r;
    reg [31:0] previous_command_r;
    reg [31:0] bounded_command_w;
    reg [31:0] raw_command_w;
    reg [31:0] clamped_command_w;
    reg [31:0] rate_limited_w;
    reg [31:0] min_bound_w;
    reg [31:0] max_bound_w;

    assign actuator_valid = actuator_valid_r;
    assign actuator_command = actuator_command_r;
    assign last_good_command = last_good_command_r;

    always @(*) begin
        raw_command_w = drag_estimate + lift_estimate + {24'h000000, confidence_flags};
        min_bound_w = actuator_min;
        max_bound_w = actuator_max;
        if (min_bound_w > max_bound_w) begin
            min_bound_w = max_bound_w;
        end
        if (raw_command_w < min_bound_w) begin
            clamped_command_w = min_bound_w;
        end else if (raw_command_w > max_bound_w) begin
            clamped_command_w = max_bound_w;
        end else begin
            clamped_command_w = raw_command_w;
        end
        if (rate_limit == 32'h00000000) begin
            rate_limited_w = clamped_command_w;
        end else if (clamped_command_w > previous_command_r) begin
            if ((clamped_command_w - previous_command_r) > rate_limit) begin
                rate_limited_w = previous_command_r + rate_limit;
            end else begin
                rate_limited_w = clamped_command_w;
            end
        end else if (previous_command_r > clamped_command_w) begin
            if ((previous_command_r - clamped_command_w) > rate_limit) begin
                rate_limited_w = previous_command_r - rate_limit;
            end else begin
                rate_limited_w = clamped_command_w;
            end
        end else begin
            rate_limited_w = clamped_command_w;
        end
        bounded_command_w = rate_limited_w;
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            actuator_valid_r <= 1'b0;
            actuator_command_r <= 32'h00000000;
            last_good_command_r <= 32'h00000000;
            previous_command_r <= 32'h00000000;
        end else begin
            if (actuator_enable && allow_command_update && !safe_mode_select) begin
                actuator_command_r <= bounded_command_w;
                last_good_command_r <= bounded_command_w;
                previous_command_r <= bounded_command_w;
                actuator_valid_r <= 1'b1;
            end else begin
                actuator_valid_r <= 1'b0;
            end
        end
    end

endmodule
