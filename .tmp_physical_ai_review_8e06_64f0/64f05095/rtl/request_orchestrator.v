module request_orchestrator (
    clk,
    rst_n,
    vehicle_geometry_valid,
    vehicle_geometry_ready,
    vehicle_geometry,
    flow_conditions_valid,
    flow_conditions_ready,
    flow_conditions,
    cfg_load_done,
    cfg_watchdog_threshold,
    cfg_reference_stream_velocity_mps,
    cfg_geometry_provenance_tag,
    request_id_out,
    timestamp_out,
    model_req_valid,
    model_req_ready,
    model_req_id,
    model_req_timestamp,
    model_req_geometry,
    model_req_stream_velocity_mps,
    model_req_geometry_tag,
    outstanding_valid,
    timeout_event
);

input clk;
input rst_n;
input vehicle_geometry_valid;
output vehicle_geometry_ready;
input [63:0] vehicle_geometry;
input flow_conditions_valid;
output flow_conditions_ready;
input [31:0] flow_conditions;
output cfg_load_done;
input [15:0] cfg_watchdog_threshold;
input [15:0] cfg_reference_stream_velocity_mps;
input [7:0] cfg_geometry_provenance_tag;
output reg [15:0] request_id_out;
output reg [15:0] timestamp_out;
output reg model_req_valid;
input model_req_ready;
output reg [15:0] model_req_id;
output reg [15:0] model_req_timestamp;
output reg [63:0] model_req_geometry;
output reg [15:0] model_req_stream_velocity_mps;
output reg [7:0] model_req_geometry_tag;
output reg outstanding_valid;
output reg timeout_event;

assign vehicle_geometry_ready = ~outstanding_valid;
assign flow_conditions_ready = ~outstanding_valid;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        request_id_out <= 16'h0000;
        timestamp_out <= 16'h0000;
        model_req_valid <= 1'b0;
        model_req_id <= 16'h0000;
        model_req_timestamp <= 16'h0000;
        model_req_geometry <= 64'h0000_0000_0000_0000;
        model_req_stream_velocity_mps <= 16'h0000;
        model_req_geometry_tag <= 8'h00;
        outstanding_valid <= 1'b0;
        timeout_event <= 1'b0;
    end else begin
        timeout_event <= outstanding_valid & (cfg_watchdog_threshold != 16'h0000);
        if (!outstanding_valid && vehicle_geometry_valid && flow_conditions_valid && cfg_load_done) begin
            outstanding_valid <= 1'b1;
            request_id_out <= request_id_out + 16'h0001;
            timestamp_out <= timestamp_out + 16'h0001;
            model_req_valid <= 1'b1;
            model_req_id <= request_id_out + 16'h0001;
            model_req_timestamp <= timestamp_out + 16'h0001;
            model_req_geometry <= vehicle_geometry;
            model_req_stream_velocity_mps <= cfg_reference_stream_velocity_mps;
            model_req_geometry_tag <= cfg_geometry_provenance_tag;
        end else if (model_req_valid && model_req_ready) begin
            outstanding_valid <= 1'b0;
            model_req_valid <= 1'b0;
        end else if (!cfg_load_done) begin
            outstanding_valid <= 1'b0;
            model_req_valid <= 1'b0;
        end
    end
end

endmodule
