module actuator_tx (
    input         clk,
    input         reset_n,
    input  [15:0] final_command_value,
    input  [3:0] final_command_mode,
    input  [7:0] safety_flags,
    input         fallback_active,
    input         out_act_ready,
    output reg    out_act_valid,
    output reg [63:0] out_act_data,
    output reg    request_pending,
    output reg    fresh_command_event,
    output reg    model_req_valid,
    output reg [63:0] model_req_data,
    input         model_req_ready,
    input         model_rsp_valid,
    input  [63:0] model_rsp_data,
    output reg    model_rsp_ready
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        out_act_valid <= 1'b0;
        out_act_data <= 64'd0;
        request_pending <= 1'b0;
        fresh_command_event <= 1'b0;
        model_req_valid <= 1'b0;
        model_req_data <= 64'd0;
        model_rsp_ready <= 1'b0;
    end else begin
        out_act_valid <= 1'b0;
        fresh_command_event <= 1'b0;
        model_rsp_ready <= 1'b1;
        if (!fallback_active || out_act_ready) begin
            out_act_valid <= 1'b1;
            out_act_data <= {4'b0, 32'd0, safety_flags, final_command_mode, final_command_value};
            fresh_command_event <= 1'b1;
        end
        request_pending <= ~out_act_ready;
        model_req_valid <= 1'b0;
        model_req_data <= {final_command_value, 48'd0};
        if (model_req_ready) begin
            model_req_valid <= 1'b1;
            model_req_data <= {final_command_value, final_command_mode, safety_flags, 36'b0};
        end
        if (model_rsp_valid) begin
            model_rsp_ready <= 1'b1;
            out_act_data <= model_rsp_data;
        end
    end
end

endmodule
