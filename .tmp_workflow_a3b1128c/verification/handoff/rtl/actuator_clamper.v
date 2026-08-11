module actuator_clamper (
    input         clk,
    input         reset_n,
    input  [15:0] validated_command_value,
    input  [3:0] validated_command_mode,
    input  [15:0] actuator_min,
    input  [15:0] actuator_max,
    input         slew_limit_enable,
    input  [7:0] slew_limit,
    input  [15:0] previous_command_value,
    output reg [15:0] clamped_command_value,
    output reg    clamp_active,
    output reg    slew_active,
    output reg [15:0] updated_previous_command_value
);

reg [15:0] target_value;
reg [15:0] delta_abs;
reg [15:0] slew_bound;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        clamped_command_value <= 16'd0;
        clamp_active <= 1'b0;
        slew_active <= 1'b0;
        updated_previous_command_value <= 16'd0;
        target_value <= 16'd0;
        delta_abs <= 16'd0;
        slew_bound <= 16'd0;
    end else begin
        target_value <= validated_command_value;
        clamp_active <= 1'b0;
        slew_active <= 1'b0;
        if (validated_command_value < actuator_min) begin
            clamped_command_value <= actuator_min;
            clamp_active <= 1'b1;
        end else if (validated_command_value > actuator_max) begin
            clamped_command_value <= actuator_max;
            clamp_active <= 1'b1;
        end else begin
            clamped_command_value <= validated_command_value;
        end
        if (slew_limit_enable) begin
            if (clamped_command_value >= previous_command_value) begin
                delta_abs <= clamped_command_value - previous_command_value;
            end else begin
                delta_abs <= previous_command_value - clamped_command_value;
            end
            slew_bound <= {8'd0, slew_limit};
            if (delta_abs > slew_bound) begin
                slew_active <= 1'b1;
                if (clamped_command_value > previous_command_value) begin
                    updated_previous_command_value <= previous_command_value + slew_bound;
                end else begin
                    updated_previous_command_value <= previous_command_value - slew_bound;
                end
            end else begin
                updated_previous_command_value <= clamped_command_value;
            end
        end else begin
            updated_previous_command_value <= clamped_command_value;
        end
    end
end

endmodule
