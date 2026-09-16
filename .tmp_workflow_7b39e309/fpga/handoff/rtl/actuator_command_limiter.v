module actuator_command_limiter(
    clk,
    reset_n,
    command_allowed,
    validated_rsp_valid,
    validated_rsp_data,
    validated_req_valid,
    validated_req_data,
    actuator_cmd_valid,
    actuator_cmd_data,
    actuator_cmd_saturated,
    actuator_cmd_latched_fault,
    fault_latched
);
input clk;
input reset_n;
input command_allowed;
input validated_rsp_valid;
input [31:0] validated_rsp_data;
input validated_req_valid;
input [31:0] validated_req_data;
output reg actuator_cmd_valid;
output reg [15:0] actuator_cmd_data;
output reg actuator_cmd_saturated;
output reg actuator_cmd_latched_fault;
output reg fault_latched;

reg [16:0] cmd_calc;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        actuator_cmd_valid <= 1'b0;
        actuator_cmd_data <= 16'h0000;
        actuator_cmd_saturated <= 1'b0;
        actuator_cmd_latched_fault <= 1'b0;
        fault_latched <= 1'b0;
        cmd_calc <= 17'h00000;
    end else begin
        cmd_calc <= {1'b0, validated_rsp_data[15:0]} + {1'b0, validated_req_data[15:0]};
        if (command_allowed && validated_rsp_valid && validated_req_valid) begin
            if (cmd_calc[16] || (cmd_calc[15:0] > 16'h7FFF)) begin
                actuator_cmd_data <= 16'h7FFF;
                actuator_cmd_saturated <= 1'b1;
            end else if (cmd_calc[15:0] < 16'h0014) begin
                actuator_cmd_data <= 16'h0014;
                actuator_cmd_saturated <= 1'b1;
            end else if (cmd_calc[15:0] > 16'h0037) begin
                actuator_cmd_data <= 16'h0037;
                actuator_cmd_saturated <= 1'b1;
            end else begin
                actuator_cmd_data <= cmd_calc[15:0];
                actuator_cmd_saturated <= 1'b0;
            end
            actuator_cmd_valid <= 1'b1;
            actuator_cmd_latched_fault <= 1'b0;
        end else begin
            actuator_cmd_valid <= 1'b0;
            actuator_cmd_saturated <= 1'b0;
            actuator_cmd_latched_fault <= 1'b1;
            fault_latched <= 1'b1;
        end
    end
end

endmodule
