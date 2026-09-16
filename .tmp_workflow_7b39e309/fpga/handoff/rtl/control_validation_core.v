module control_validation_core(
    clk,
    reset_n,
    host_cmd_valid,
    host_cmd_opcode,
    host_cmd_data,
    sensor_airdata_valid,
    sensor_airspeed,
    sensor_altitude,
    sensor_angle_of_attack,
    sensor_gload,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    fault_latched,
    status_valid,
    status_code,
    validated_req_valid,
    validated_req_data,
    validated_rsp_valid,
    validated_rsp_data,
    command_allowed
);
input clk;
input reset_n;
input host_cmd_valid;
input [7:0] host_cmd_opcode;
input [31:0] host_cmd_data;
input sensor_airdata_valid;
input [15:0] sensor_airspeed;
input [15:0] sensor_altitude;
input [15:0] sensor_angle_of_attack;
input [15:0] sensor_gload;
input model_req_valid;
input [31:0] model_req_data;
input model_req_ready;
input model_rsp_valid;
input [31:0] model_rsp_data;
output reg model_rsp_ready;
output reg fault_latched;
output reg status_valid;
output reg [7:0] status_code;
output reg validated_req_valid;
output reg [31:0] validated_req_data;
output reg validated_rsp_valid;
output reg [31:0] validated_rsp_data;
output reg command_allowed;

reg [7:0] timeout_ctr;
reg [31:0] req_shadow;
reg [31:0] rsp_shadow;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_rsp_ready <= 1'b0;
        fault_latched <= 1'b0;
        status_valid <= 1'b0;
        status_code <= 8'h00;
        validated_req_valid <= 1'b0;
        validated_req_data <= 32'h00000000;
        validated_rsp_valid <= 1'b0;
        validated_rsp_data <= 32'h00000000;
        command_allowed <= 1'b0;
        timeout_ctr <= 8'h00;
        req_shadow <= 32'h00000000;
        rsp_shadow <= 32'h00000000;
    end else begin
        model_rsp_ready <= model_req_valid & model_req_ready & sensor_airdata_valid;
        status_valid <= host_cmd_valid | sensor_airdata_valid | model_rsp_valid;
        status_code <= fault_latched ? 8'hE1 :
                       (!sensor_airdata_valid ? 8'h21 :
                       (!model_req_valid ? 8'h11 :
                       (!model_rsp_valid ? 8'h12 :
                       8'h00)));
        validated_req_valid <= host_cmd_valid & sensor_airdata_valid & (host_cmd_opcode != 8'h00);
        validated_req_data <= model_req_data ^ host_cmd_data;
        validated_rsp_valid <= model_rsp_valid & model_rsp_ready;
        validated_rsp_data <= model_rsp_data ^ req_shadow;
        command_allowed <= sensor_airdata_valid & model_rsp_valid & model_req_valid & ~fault_latched;
        if (validated_req_valid) begin
            req_shadow <= validated_req_data;
        end
        if (validated_rsp_valid) begin
            rsp_shadow <= validated_rsp_data;
        end
        if (model_req_valid && model_req_ready) begin
            timeout_ctr <= 8'h00;
        end else if (sensor_airdata_valid) begin
            timeout_ctr <= timeout_ctr + 8'h01;
        end
        if ((timeout_ctr > 8'h20) || (!sensor_airdata_valid && host_cmd_valid)) begin
            fault_latched <= 1'b1;
        end
        if (model_rsp_valid && !model_rsp_ready) begin
            fault_latched <= 1'b1;
        end
    end
end

endmodule
