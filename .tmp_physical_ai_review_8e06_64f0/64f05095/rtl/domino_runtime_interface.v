module domino_runtime_interface (
    clk,
    rst_n,
    model_req_valid,
    model_req_ready,
    model_req_id,
    model_req_timestamp,
    model_req_geometry,
    model_req_stream_velocity_mps,
    model_req_geometry_tag,
    model_resp_ready,
    model_resp_valid,
    model_resp_id,
    model_resp_timestamp,
    model_resp_drag_force,
    model_resp_lift_force,
    model_resp_surface_pressure,
    model_resp_flow_field_meta,
    response_match,
    freshness_ok,
    response_valid_qualified,
    response_drag_force,
    response_lift_force,
    response_surface_pressure,
    response_flow_field_meta,
    stale_or_mismatch_fault
);

input clk;
input rst_n;
input model_req_valid;
output model_req_ready;
input [15:0] model_req_id;
input [15:0] model_req_timestamp;
input [63:0] model_req_geometry;
input [15:0] model_req_stream_velocity_mps;
input [7:0] model_req_geometry_tag;
output model_resp_ready;
input model_resp_valid;
input [15:0] model_resp_id;
input [15:0] model_resp_timestamp;
input [23:0] model_resp_drag_force;
input [23:0] model_resp_lift_force;
input [15:0] model_resp_surface_pressure;
input [15:0] model_resp_flow_field_meta;
output reg response_match;
output reg freshness_ok;
output reg response_valid_qualified;
output reg [23:0] response_drag_force;
output reg [23:0] response_lift_force;
output reg [15:0] response_surface_pressure;
output reg [15:0] response_flow_field_meta;
output reg stale_or_mismatch_fault;

assign model_req_ready = 1'b1;
assign model_resp_ready = 1'b1;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        response_match <= 1'b0;
        freshness_ok <= 1'b0;
        response_valid_qualified <= 1'b0;
        response_drag_force <= 24'h000000;
        response_lift_force <= 24'h000000;
        response_surface_pressure <= 16'h0000;
        response_flow_field_meta <= 16'h0000;
        stale_or_mismatch_fault <= 1'b0;
    end else begin
        response_match <= model_resp_valid & (model_resp_id == model_req_id);
        freshness_ok <= model_resp_valid & (model_resp_id == model_req_id) & (model_resp_timestamp >= model_req_timestamp);
        response_valid_qualified <= model_resp_valid & (model_resp_id == model_req_id) & (model_resp_timestamp >= model_req_timestamp);
        stale_or_mismatch_fault <= model_resp_valid & ~((model_resp_id == model_req_id) & (model_resp_timestamp >= model_req_timestamp));
        if (model_resp_valid & (model_resp_id == model_req_id) & (model_resp_timestamp >= model_req_timestamp)) begin
            response_drag_force <= model_resp_drag_force;
            response_lift_force <= model_resp_lift_force;
            response_surface_pressure <= model_resp_surface_pressure;
            response_flow_field_meta <= model_resp_flow_field_meta;
        end
    end
end

endmodule
