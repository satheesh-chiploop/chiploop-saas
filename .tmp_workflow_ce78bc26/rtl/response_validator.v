module response_validator (
    clk,
    reset_n,
    resp_valid,
    resp_id,
    resp_timestamp,
    resp_payload,
    outstanding_req_id,
    outstanding_req_timestamp,
    fresh_response_pulse,
    response_mismatch,
    model_output_valid,
    drag_force,
    lift_force,
    surface_pressure,
    flow_field_metadata,
    stale_response
);
input clk;
input reset_n;
input resp_valid;
input [15:0] resp_id;
input [31:0] resp_timestamp;
input [255:0] resp_payload;
input [15:0] outstanding_req_id;
input [31:0] outstanding_req_timestamp;
input fresh_response_pulse;
input response_mismatch;
output model_output_valid;
output [31:0] drag_force;
output [31:0] lift_force;
output [31:0] surface_pressure;
output [127:0] flow_field_metadata;
output stale_response;

reg model_output_valid_r;
reg [31:0] drag_force_r;
reg [31:0] lift_force_r;
reg [31:0] surface_pressure_r;
reg [127:0] flow_field_metadata_r;
reg stale_response_r;

wire response_match;
wire response_fresh;

assign response_match = resp_valid & (resp_id == outstanding_req_id);
assign response_fresh = response_match & (resp_timestamp >= outstanding_req_timestamp);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_output_valid_r <= 1'b0;
        drag_force_r <= 32'h00000000;
        lift_force_r <= 32'h00000000;
        surface_pressure_r <= 32'h00000000;
        flow_field_metadata_r <= 128'h00000000000000000000000000000000;
        stale_response_r <= 1'b0;
    end else begin
        model_output_valid_r <= response_fresh & fresh_response_pulse & ~response_mismatch;
        stale_response_r <= resp_valid & ~response_fresh;
        if (response_fresh & fresh_response_pulse & ~response_mismatch) begin
            drag_force_r <= resp_payload[31:0];
            lift_force_r <= resp_payload[63:32];
            surface_pressure_r <= resp_payload[95:64];
            flow_field_metadata_r <= {resp_payload[255:128]};
        end
    end
end

assign model_output_valid = model_output_valid_r;
assign drag_force = drag_force_r;
assign lift_force = lift_force_r;
assign surface_pressure = surface_pressure_r;
assign flow_field_metadata = flow_field_metadata_r;
assign stale_response = stale_response_r;

endmodule
