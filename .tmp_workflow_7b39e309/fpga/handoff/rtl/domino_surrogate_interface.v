module domino_surrogate_interface(
    clk,
    reset_n,
    validated_req_valid,
    validated_req_data,
    validated_rsp_valid,
    validated_rsp_data,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    payload_csb_n,
    payload_we_n,
    payload_addr,
    payload_din,
    payload_dout,
    model_trace_valid,
    model_trace_data
);
input clk;
input reset_n;
input validated_req_valid;
input [31:0] validated_req_data;
input validated_rsp_valid;
input [31:0] validated_rsp_data;
output reg model_req_valid;
output reg [31:0] model_req_data;
input model_req_ready;
input model_rsp_valid;
input [31:0] model_rsp_data;
output reg model_rsp_ready;
output reg payload_csb_n;
output reg payload_we_n;
output reg [6:0] payload_addr;
output reg [31:0] payload_din;
input [31:0] payload_dout;
output reg model_trace_valid;
output reg [31:0] model_trace_data;
reg [6:0] payload_ptr;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_req_valid <= 1'b0;
        model_req_data <= 32'h00000000;
        model_rsp_ready <= 1'b0;
        payload_csb_n <= 1'b1;
        payload_we_n <= 1'b1;
        payload_addr <= 7'h00;
        payload_din <= 32'h00000000;
        model_trace_valid <= 1'b0;
        model_trace_data <= 32'h00000000;
        payload_ptr <= 7'h00;
    end else begin
        model_req_valid <= validated_req_valid;
        model_req_data <= validated_req_data ^ payload_dout;
        model_rsp_ready <= validated_rsp_valid & model_req_ready;
        payload_csb_n <= ~(validated_req_valid | validated_rsp_valid);
        payload_we_n <= ~(validated_req_valid & model_req_ready);
        payload_addr <= payload_ptr;
        payload_din <= validated_req_data ^ validated_rsp_data;
        model_trace_valid <= validated_req_valid | validated_rsp_valid;
        model_trace_data <= {validated_rsp_data[15:0], validated_req_data[15:0]};
        if (validated_req_valid || validated_rsp_valid) begin
            payload_ptr <= payload_ptr + 7'h01;
        end
    end
end

endmodule
