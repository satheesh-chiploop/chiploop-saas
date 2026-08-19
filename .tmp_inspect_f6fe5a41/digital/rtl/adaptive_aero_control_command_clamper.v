module adaptive_aero_control_command_clamper (
    clk,
    reset_n,
    command_enable_i,
    response_valid_i,
    response_drag_i,
    response_lift_i,
    cfg_clamp_min_i,
    cfg_clamp_max_i,
    actuator_cmd_o,
    actuator_cmd_valid_o,
    command_clamped_o
);
input clk;
input reset_n;
input command_enable_i;
input response_valid_i;
input [31:0] response_drag_i;
input [31:0] response_lift_i;
input [31:0] cfg_clamp_min_i;
input [31:0] cfg_clamp_max_i;
output [31:0] actuator_cmd_o;
output actuator_cmd_valid_o;
output command_clamped_o;

reg [31:0] actuator_cmd_r;
reg actuator_cmd_valid_r;
reg command_clamped_r;
reg [31:0] selected_cmd;

assign actuator_cmd_o = actuator_cmd_r;
assign actuator_cmd_valid_o = actuator_cmd_valid_r;
assign command_clamped_o = command_clamped_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        actuator_cmd_r <= 32'h00000000;
        actuator_cmd_valid_r <= 1'b0;
        command_clamped_r <= 1'b0;
        selected_cmd <= 32'h00000000;
    end else begin
        if (command_enable_i && response_valid_i) begin
            if (response_drag_i >= response_lift_i)
                selected_cmd <= response_drag_i;
            else
                selected_cmd <= response_lift_i;
            if (selected_cmd < cfg_clamp_min_i) begin
                actuator_cmd_r <= cfg_clamp_min_i;
                command_clamped_r <= 1'b1;
            end else if (selected_cmd > cfg_clamp_max_i) begin
                actuator_cmd_r <= cfg_clamp_max_i;
                command_clamped_r <= 1'b1;
            end else begin
                actuator_cmd_r <= selected_cmd;
                command_clamped_r <= 1'b0;
            end
            actuator_cmd_valid_r <= 1'b1;
        end else begin
            actuator_cmd_valid_r <= 1'b0;
            command_clamped_r <= 1'b0;
        end
    end
end
endmodule
