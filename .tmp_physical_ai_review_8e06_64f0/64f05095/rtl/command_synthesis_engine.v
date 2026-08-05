module command_synthesis_engine (
    clk,
    rst_n,
    response_valid_qualified,
    response_drag_force,
    response_lift_force,
    response_surface_pressure,
    response_flow_field_meta,
    cfg_cmd_gain_drag,
    cfg_cmd_gain_lift,
    cfg_cmd_bias,
    raw_actuator_cmd,
    raw_cmd_valid
);

input clk;
input rst_n;
input response_valid_qualified;
input [23:0] response_drag_force;
input [23:0] response_lift_force;
input [15:0] response_surface_pressure;
input [15:0] response_flow_field_meta;
input [15:0] cfg_cmd_gain_drag;
input [15:0] cfg_cmd_gain_lift;
input [31:0] cfg_cmd_bias;
output reg [31:0] raw_actuator_cmd;
output reg raw_cmd_valid;

reg signed [31:0] drag_term;
reg signed [31:0] lift_term;
reg signed [31:0] pressure_term;
reg signed [31:0] meta_term;
reg signed [31:0] sum_term;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        raw_actuator_cmd <= 32'h00000000;
        raw_cmd_valid <= 1'b0;
        drag_term <= 32'sd0;
        lift_term <= 32'sd0;
        pressure_term <= 32'sd0;
        meta_term <= 32'sd0;
        sum_term <= 32'sd0;
    end else begin
        raw_cmd_valid <= response_valid_qualified;
        drag_term <= $signed({1'b0, response_drag_force[23:8]}) * $signed({1'b0, cfg_cmd_gain_drag});
        lift_term <= $signed({1'b0, response_lift_force[23:8]}) * $signed({1'b0, cfg_cmd_gain_lift});
        pressure_term <= $signed({16'b0, response_surface_pressure}) >>> 1;
        meta_term <= $signed({16'b0, response_flow_field_meta}) >>> 2;
        sum_term <= drag_term + lift_term + pressure_term + meta_term + $signed(cfg_cmd_bias);
        if (response_valid_qualified) begin
            raw_actuator_cmd <= sum_term[31:0];
        end else begin
            raw_actuator_cmd <= 32'h00000000;
        end
    end
end

endmodule
