module ag_request_sequencer(
    clk,
    rst_n,
    geometry_valid,
    flow_valid,
    configuration_valid,
    safety_inhibit,
    sanitized_geometry,
    sanitized_flow,
    geometry_revision,
    reference_operating_tag,
    request_id_out,
    request_timestamp,
    request_age,
    request_valid,
    o_model_request,
    request_issued
);
input clk;
input rst_n;
input geometry_valid;
input flow_valid;
input configuration_valid;
input safety_inhibit;
input [127:0] sanitized_geometry;
input [95:0] sanitized_flow;
input [15:0] geometry_revision;
input [15:0] reference_operating_tag;
output [15:0] request_id_out;
output [15:0] request_timestamp;
output [15:0] request_age;
output request_valid;
output [255:0] o_model_request;
output request_issued;

reg [15:0] request_id_r;
reg [15:0] request_timestamp_r;
reg [15:0] request_age_r;
reg request_valid_r;
reg [255:0] o_model_request_r;
reg request_issued_r;

wire issue_en;
wire [15:0] next_request_id;
wire [15:0] next_timestamp;
wire [15:0] next_age;
wire [255:0] request_payload_w;

assign issue_en = geometry_valid & flow_valid & configuration_valid & ~safety_inhibit;
assign next_request_id = request_id_r + 16'h0001;
assign next_timestamp = request_timestamp_r + 16'h0001;
assign next_age = request_age_r + 16'h0001;
assign request_payload_w = {reference_operating_tag, geometry_revision, sanitized_flow, sanitized_geometry[95:0], 16'h0000};

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        request_id_r <= 16'h0000;
        request_timestamp_r <= 16'h0000;
        request_age_r <= 16'h0000;
        request_valid_r <= 1'b0;
        o_model_request_r <= 256'h0000000000000000000000000000000000000000000000000000000000000000;
        request_issued_r <= 1'b0;
    end else begin
        request_valid_r <= issue_en;
        request_issued_r <= issue_en;
        if (issue_en) begin
            request_id_r <= next_request_id;
            request_timestamp_r <= next_timestamp;
            request_age_r <= 16'h0000;
            o_model_request_r <= request_payload_w;
        end else begin
            request_age_r <= next_age;
        end
    end
end

assign request_id_out = request_id_r;
assign request_timestamp = request_timestamp_r;
assign request_age = request_age_r;
assign request_valid = request_valid_r;
assign o_model_request = o_model_request_r;
assign request_issued = request_issued_r;

endmodule
