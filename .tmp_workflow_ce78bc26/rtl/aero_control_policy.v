module aero_control_policy (
    clk,
    reset_n,
    model_output_valid,
    drag_force,
    lift_force,
    surface_pressure,
    flow_field_metadata,
    command_enable,
    command_vector
);
input clk;
input reset_n;
input model_output_valid;
input [31:0] drag_force;
input [31:0] lift_force;
input [31:0] surface_pressure;
input [127:0] flow_field_metadata;
output command_enable;
output [63:0] command_vector;
reg command_enable_r;
reg [63:0] command_vector_r;
always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        command_enable_r <= 1'b0;
        command_vector_r <= 64'h0000000000000000;
    end else begin
        command_enable_r <= model_output_valid;
        if (model_output_valid) begin
            command_vector_r <= {drag_force[15:0] ^ lift_force[15:0], surface_pressure[15:0] ^ flow_field_metadata[15:0], drag_force[31:16] + lift_force[31:16], surface_pressure[31:16] + flow_field_metadata[31:16]};
        end
    end
end

assign command_enable = command_enable_r;
assign command_vector = command_vector_r;

endmodule
