module actuator_command_shaper (
    input         clk,
    input         rst_n,
    input         validated_response_valid,
    input  [31:0] validated_response_data,
    input  [31:0] cfg_actuator_min,
    input  [31:0] cfg_actuator_max,
    input         cfg_slew_enable,
    input  [15:0] cfg_slew_limit,
    input         safe_fallback,
    input         fault_latched,
    output reg [31:0] actuator_cmd,
    output reg    actuator_cmd_valid,
    output reg [31:0] last_good_cmd
);

reg [31:0] prev_cmd;
reg [31:0] clamped_cmd;
reg [31:0] slew_cmd;
reg [31:0] diff_mag;
reg [31:0] lower_bound;
reg [31:0] upper_bound;

always @(*) begin
    lower_bound = cfg_actuator_min;
    upper_bound = cfg_actuator_max;
    if (lower_bound > upper_bound) begin
        lower_bound = cfg_actuator_max;
        upper_bound = cfg_actuator_min;
    end
    if (validated_response_data < lower_bound) begin
        clamped_cmd = lower_bound;
    end else if (validated_response_data > upper_bound) begin
        clamped_cmd = upper_bound;
    end else begin
        clamped_cmd = validated_response_data;
    end
    if (cfg_slew_enable) begin
        if (clamped_cmd >= prev_cmd) begin
            diff_mag = clamped_cmd - prev_cmd;
            if (diff_mag > {16'h0000, cfg_slew_limit}) slew_cmd = prev_cmd + {16'h0000, cfg_slew_limit};
            else slew_cmd = clamped_cmd;
        end else begin
            diff_mag = prev_cmd - clamped_cmd;
            if (diff_mag > {16'h0000, cfg_slew_limit}) slew_cmd = prev_cmd - {16'h0000, cfg_slew_limit};
            else slew_cmd = clamped_cmd;
        end
    end else begin
        slew_cmd = clamped_cmd;
        diff_mag = 32'h00000000;
    end
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        actuator_cmd <= 32'h00000000;
        actuator_cmd_valid <= 1'b0;
        last_good_cmd <= 32'h00000000;
        prev_cmd <= 32'h00000000;
    end else begin
        actuator_cmd_valid <= 1'b0;
        if (validated_response_valid && !safe_fallback && !fault_latched) begin
            actuator_cmd <= slew_cmd;
            last_good_cmd <= slew_cmd;
            prev_cmd <= slew_cmd;
            actuator_cmd_valid <= 1'b1;
        end
        if (safe_fallback || fault_latched) begin
            actuator_cmd_valid <= 1'b0;
        end
    end
end

endmodule
