module domino_model_request_manager (
    clk,
    rst_n,
    cfg_enable,
    cfg_request_timeout_cycles,
    validated_stream_velocity_mps,
    geometry_handle_canonical,
    active_epoch,
    geometry_valid,
    flow_valid,
    envelope_in_range,
    cfg_fault,
    geometry_fault,
    flow_fault,
    model_req_ready,
    request_arm,
    model_req_valid,
    model_req_id,
    model_req_epoch,
    model_req_geometry_handle,
    model_req_stream_velocity_mps,
    model_req_timeout_cycles,
    request_outstanding,
    request_timeout_fault,
    last_issued_req_id
);
input clk;
input rst_n;
input cfg_enable;
input [15:0] cfg_request_timeout_cycles;
input [15:0] validated_stream_velocity_mps;
input [31:0] geometry_handle_canonical;
input [31:0] active_epoch;
input geometry_valid;
input flow_valid;
input envelope_in_range;
input cfg_fault;
input geometry_fault;
input flow_fault;
input model_req_ready;
input request_arm;
output reg model_req_valid;
output reg [31:0] model_req_id;
output reg [31:0] model_req_epoch;
output reg [31:0] model_req_geometry_handle;
output reg [15:0] model_req_stream_velocity_mps;
output reg [15:0] model_req_timeout_cycles;
output reg request_outstanding;
output reg request_timeout_fault;
output reg [31:0] last_issued_req_id;
reg [15:0] age_count;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        model_req_valid <= 1'b0;
        model_req_id <= 32'h00000000;
        model_req_epoch <= 32'h00000000;
        model_req_geometry_handle <= 32'h00000000;
        model_req_stream_velocity_mps <= 16'h0000;
        model_req_timeout_cycles <= 16'h0000;
        request_outstanding <= 1'b0;
        request_timeout_fault <= 1'b0;
        last_issued_req_id <= 32'h00000000;
        age_count <= 16'h0000;
    end else begin
        model_req_timeout_cycles <= cfg_request_timeout_cycles;
        if (cfg_enable && !cfg_fault && !geometry_fault && !flow_fault && geometry_valid && flow_valid && envelope_in_range && request_arm) begin
            model_req_valid <= 1'b1;
            model_req_id <= last_issued_req_id + 32'h00000001;
            model_req_epoch <= active_epoch;
            model_req_geometry_handle <= geometry_handle_canonical;
            model_req_stream_velocity_mps <= validated_stream_velocity_mps;
            request_outstanding <= 1'b1;
            age_count <= 16'h0000;
            last_issued_req_id <= last_issued_req_id + 32'h00000001;
        end else if (model_req_valid && model_req_ready) begin
            model_req_valid <= 1'b0;
            request_outstanding <= 1'b1;
            age_count <= 16'h0000;
        end else begin
            if (request_outstanding) begin
                age_count <= age_count + 16'h0001;
                if (age_count >= cfg_request_timeout_cycles) begin
                    request_timeout_fault <= 1'b1;
                    request_outstanding <= 1'b0;
                    model_req_valid <= 1'b0;
                end
            end
        end
    end
end
endmodule
