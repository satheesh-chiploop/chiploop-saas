module model_txn_mgr (
    clk,
    reset_n,
    geometry_valid,
    geometry_descriptor,
    flow_valid,
    flow_descriptor,
    safe_mode,
    fallback_active,
    req_ready,
    resp_valid,
    resp_id,
    resp_timestamp,
    resp_payload,
    req_valid,
    req_id,
    req_payload,
    request_outstanding,
    outstanding_req_id,
    outstanding_req_timestamp,
    fresh_response_pulse,
    response_mismatch,
    response_fresh,
    validated_resp_payload
);
input clk;
input reset_n;
input geometry_valid;
input [127:0] geometry_descriptor;
input flow_valid;
input [63:0] flow_descriptor;
input safe_mode;
input fallback_active;
input req_ready;
input resp_valid;
input [15:0] resp_id;
input [31:0] resp_timestamp;
input [255:0] resp_payload;
output req_valid;
output [15:0] req_id;
output [319:0] req_payload;
output request_outstanding;
output [15:0] outstanding_req_id;
output [31:0] outstanding_req_timestamp;
output fresh_response_pulse;
output response_mismatch;
output response_fresh;
output [255:0] validated_resp_payload;
reg [15:0] request_id_r;
reg req_valid_r;
reg request_outstanding_r;
reg [15:0] outstanding_req_id_r;
reg [31:0] outstanding_req_timestamp_r;
reg fresh_response_pulse_r;
reg response_mismatch_r;
reg response_fresh_r;
reg [255:0] validated_resp_payload_r;
reg [31:0] timebase_r;
reg [319:0] req_payload_r;
reg [319:0] req_payload_next;

wire request_can_issue;
wire response_is_match;
wire response_is_fresh;
wire response_is_bad;
wire request_timestamp_match;

assign request_can_issue = geometry_valid & flow_valid & ~safe_mode & ~fallback_active & req_ready & ~request_outstanding_r;
assign request_timestamp_match = 1'b1;
assign response_is_match = resp_valid & request_outstanding_r & (resp_id == outstanding_req_id_r);
assign response_is_fresh = response_is_match & (resp_timestamp >= outstanding_req_timestamp_r);
assign response_is_bad = resp_valid & (~request_outstanding_r | (resp_id != outstanding_req_id_r) | (resp_timestamp < outstanding_req_timestamp_r));

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        request_id_r <= 16'h0000;
        req_valid_r <= 1'b0;
        request_outstanding_r <= 1'b0;
        outstanding_req_id_r <= 16'h0000;
        outstanding_req_timestamp_r <= 32'h00000000;
        fresh_response_pulse_r <= 1'b0;
        response_mismatch_r <= 1'b0;
        response_fresh_r <= 1'b0;
        validated_resp_payload_r <= 256'h0000000000000000000000000000000000000000000000000000000000000000;
        timebase_r <= 32'h00000000;
        req_payload_r <= 320'h00000000000000000000000000000000000000000000000000000000000000000000000000000000;
    end else begin
        timebase_r <= timebase_r + 32'd1;
        fresh_response_pulse_r <= 1'b0;
        if (request_can_issue) begin
            req_valid_r <= 1'b1;
            request_outstanding_r <= 1'b1;
            outstanding_req_id_r <= request_id_r;
            outstanding_req_timestamp_r <= timebase_r;
            req_payload_r <= {request_id_r, geometry_descriptor, flow_descriptor, timebase_r};
            request_id_r <= request_id_r + 16'd1;
        end else begin
            req_valid_r <= 1'b0;
        end
        response_mismatch_r <= response_is_bad;
        response_fresh_r <= 1'b0;
        if (response_is_fresh) begin
            response_fresh_r <= 1'b1;
            fresh_response_pulse_r <= 1'b1;
            validated_resp_payload_r <= resp_payload;
            request_outstanding_r <= 1'b0;
        end
    end
end

always @(*) begin
    req_payload_next = req_payload_r;
    if (request_can_issue) begin
        req_payload_next = {request_id_r, geometry_descriptor, flow_descriptor, timebase_r};
    end
end

assign req_valid = req_valid_r;
assign req_id = request_id_r;
assign req_payload = req_payload_r;
assign request_outstanding = request_outstanding_r;
assign outstanding_req_id = outstanding_req_id_r;
assign outstanding_req_timestamp = outstanding_req_timestamp_r;
assign fresh_response_pulse = fresh_response_pulse_r;
assign response_mismatch = response_mismatch_r;
assign response_fresh = response_fresh_r;
assign validated_resp_payload = validated_resp_payload_r;

endmodule
