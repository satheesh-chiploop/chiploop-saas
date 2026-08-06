module domino_model_response_validator (
    clk,
    rst_n,
    request_outstanding,
    last_issued_req_id,
    active_epoch,
    request_timeout_fault,
    model_rsp_valid,
    model_rsp_id,
    model_rsp_epoch,
    model_rsp_status_valid,
    model_rsp_status_unavailable,
    model_rsp_drag_force,
    model_rsp_lift_force,
    model_rsp_surface_pressure,
    model_rsp_flow_field_meta,
    validated_response_valid,
    validated_rsp_id,
    validated_rsp_epoch,
    response_mismatch_fault,
    stale_response_fault,
    model_unavailable_fault,
    last_accepted_rsp_id,
    validated_model_intent,
    validated_model_intent_valid,
    stale_status
);
input clk;
input rst_n;
input request_outstanding;
input [31:0] last_issued_req_id;
input [31:0] active_epoch;
input request_timeout_fault;
input model_rsp_valid;
input [31:0] model_rsp_id;
input [31:0] model_rsp_epoch;
input model_rsp_status_valid;
input model_rsp_status_unavailable;
input [31:0] model_rsp_drag_force;
input [31:0] model_rsp_lift_force;
input [31:0] model_rsp_surface_pressure;
input [31:0] model_rsp_flow_field_meta;
output reg validated_response_valid;
output reg [31:0] validated_rsp_id;
output reg [31:0] validated_rsp_epoch;
output reg response_mismatch_fault;
output reg stale_response_fault;
output reg model_unavailable_fault;
output reg [31:0] last_accepted_rsp_id;
output reg [15:0] validated_model_intent;
output reg validated_model_intent_valid;
output reg stale_status;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        validated_response_valid <= 1'b0;
        validated_rsp_id <= 32'h00000000;
        validated_rsp_epoch <= 32'h00000000;
        response_mismatch_fault <= 1'b0;
        stale_response_fault <= 1'b0;
        model_unavailable_fault <= 1'b0;
        last_accepted_rsp_id <= 32'h00000000;
        validated_model_intent <= 16'h0000;
        validated_model_intent_valid <= 1'b0;
        stale_status <= 1'b0;
    end else begin
        validated_response_valid <= 1'b0;
        validated_model_intent_valid <= 1'b0;
        stale_status <= 1'b0;
        if (model_rsp_valid) begin
            if (!request_outstanding || request_timeout_fault) begin
                stale_response_fault <= 1'b1;
                stale_status <= 1'b1;
            end else if ((model_rsp_id == last_issued_req_id) && (model_rsp_epoch == active_epoch)) begin
                validated_response_valid <= model_rsp_status_valid;
                validated_rsp_id <= model_rsp_id;
                validated_rsp_epoch <= model_rsp_epoch;
                last_accepted_rsp_id <= model_rsp_id;
                validated_model_intent <= model_rsp_id[15:0] ^ model_rsp_epoch[15:0];
                validated_model_intent_valid <= model_rsp_status_valid & ~model_rsp_status_unavailable;
                if (model_rsp_status_unavailable) begin
                    model_unavailable_fault <= 1'b1;
                end
            end else begin
                response_mismatch_fault <= 1'b1;
                stale_response_fault <= 1'b1;
                stale_status <= 1'b1;
            end
        end
        if (model_rsp_status_unavailable) begin
            model_unavailable_fault <= 1'b1;
        end
        if (request_timeout_fault) begin
            stale_response_fault <= 1'b1;
            stale_status <= 1'b1;
        end
        if ((model_rsp_id != last_issued_req_id) && model_rsp_valid) begin
            response_mismatch_fault <= 1'b1;
        end
        if (model_rsp_flow_field_meta[0]) begin
            validated_model_intent <= validated_model_intent ^ 16'h0001;
        end
        if (model_rsp_drag_force[0]) begin
            validated_model_intent <= validated_model_intent ^ 16'h0002;
        end
        if (model_rsp_lift_force[0]) begin
            validated_model_intent <= validated_model_intent ^ 16'h0004;
        end
        if (model_rsp_surface_pressure[0]) begin
            validated_model_intent <= validated_model_intent ^ 16'h0008;
        end
    end
end
endmodule
