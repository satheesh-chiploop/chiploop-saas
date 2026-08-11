module adaptive_aero_control_top_actuator (
    clk,
    reset,
    cfg_signed_clamp,
    cfg_act0_min,
    cfg_act0_max,
    cfg_act1_min,
    cfg_act1_max,
    cfg_act2_min,
    cfg_act2_max,
    cfg_act3_min,
    cfg_act3_max,
    fallback_active,
    input_cmd_valid,
    input_cmd_ready,
    input_cmd_data,
    output_cmd_valid,
    output_cmd_ready,
    output_cmd_data
);

input clk;
input reset;
input cfg_signed_clamp;
input [15:0] cfg_act0_min;
input [15:0] cfg_act0_max;
input [15:0] cfg_act1_min;
input [15:0] cfg_act1_max;
input [15:0] cfg_act2_min;
input [15:0] cfg_act2_max;
input [15:0] cfg_act3_min;
input [15:0] cfg_act3_max;
input fallback_active;
input input_cmd_valid;
output reg input_cmd_ready;
input [63:0] input_cmd_data;
output reg output_cmd_valid;
input output_cmd_ready;
output reg [63:0] output_cmd_data;
reg [63:0] safe_cmd;
reg [63:0] clamped_cmd;
reg [15:0] ch0;
reg [15:0] ch1;
reg [15:0] ch2;
reg [15:0] ch3;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        input_cmd_ready <= 1'b1;
        output_cmd_valid <= 1'b0;
        output_cmd_data <= 64'h0000000000000000;
        safe_cmd <= 64'h0000000000000000;
        clamped_cmd <= 64'h0000000000000000;
        ch0 <= 16'h0000;
        ch1 <= 16'h0000;
        ch2 <= 16'h0000;
        ch3 <= 16'h0000;
    end else begin
        input_cmd_ready <= output_cmd_ready;
        if (fallback_active || !input_cmd_valid) begin
            safe_cmd <= 64'h0000000000000000;
        end else begin
            ch0 <= input_cmd_data[15:0];
            ch1 <= input_cmd_data[31:16];
            ch2 <= input_cmd_data[47:32];
            ch3 <= input_cmd_data[63:48];
            if (cfg_signed_clamp) begin
                if ($signed(input_cmd_data[15:0]) < $signed(cfg_act0_min)) ch0 <= cfg_act0_min;
                else if ($signed(input_cmd_data[15:0]) > $signed(cfg_act0_max)) ch0 <= cfg_act0_max;
                if ($signed(input_cmd_data[31:16]) < $signed(cfg_act1_min)) ch1 <= cfg_act1_min;
                else if ($signed(input_cmd_data[31:16]) > $signed(cfg_act1_max)) ch1 <= cfg_act1_max;
                if ($signed(input_cmd_data[47:32]) < $signed(cfg_act2_min)) ch2 <= cfg_act2_min;
                else if ($signed(input_cmd_data[47:32]) > $signed(cfg_act2_max)) ch2 <= cfg_act2_max;
                if ($signed(input_cmd_data[63:48]) < $signed(cfg_act3_min)) ch3 <= cfg_act3_min;
                else if ($signed(input_cmd_data[63:48]) > $signed(cfg_act3_max)) ch3 <= cfg_act3_max;
            end else begin
                if (input_cmd_data[15:0] < cfg_act0_min) ch0 <= cfg_act0_min;
                else if (input_cmd_data[15:0] > cfg_act0_max) ch0 <= cfg_act0_max;
                if (input_cmd_data[31:16] < cfg_act1_min) ch1 <= cfg_act1_min;
                else if (input_cmd_data[31:16] > cfg_act1_max) ch1 <= cfg_act1_max;
                if (input_cmd_data[47:32] < cfg_act2_min) ch2 <= cfg_act2_min;
                else if (input_cmd_data[47:32] > cfg_act2_max) ch2 <= cfg_act2_max;
                if (input_cmd_data[63:48] < cfg_act3_min) ch3 <= cfg_act3_min;
                else if (input_cmd_data[63:48] > cfg_act3_max) ch3 <= cfg_act3_max;
            end
            clamped_cmd <= {ch3, ch2, ch1, ch0};
        end
        if (fallback_active) begin
            output_cmd_data <= 64'h0000000000000000;
            output_cmd_valid <= 1'b1;
        end else if (input_cmd_valid) begin
            output_cmd_data <= clamped_cmd;
            output_cmd_valid <= 1'b1;
        end else if (output_cmd_ready) begin
            output_cmd_valid <= 1'b0;
        end
    end
end

endmodule
