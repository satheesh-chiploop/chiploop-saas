module adaptive_aero_transport (
    input         clk,
    input         reset_n,
    input         cfg_enable,
    input         cfg_surrogate_select,
    input         model_req_ready,
    output reg    model_req_valid,
    output reg [63:0] model_req_data,
    input         model_rsp_valid,
    input  [127:0] model_rsp_data,
    output reg    model_rsp_ready,
    input  [31:0] pack_vehicle_state,
    input  [15:0] pack_wind_state,
    input  [15:0] pack_reference_state,
    output reg    request_busy,
    output reg    response_valid,
    output reg [127:0] response_data,
    output reg    response_stale
);

reg [3:0] age_cnt;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_req_valid <= 1'b0;
        model_req_data <= 64'd0;
        model_rsp_ready <= 1'b0;
        request_busy <= 1'b0;
        response_valid <= 1'b0;
        response_data <= 128'd0;
        response_stale <= 1'b0;
        age_cnt <= 4'd0;
    end else begin
        model_rsp_ready <= cfg_enable;
        response_valid <= 1'b0;
        response_stale <= 1'b0;
        if (cfg_enable) begin
            model_req_data <= {pack_vehicle_state[31:0], pack_wind_state[15:0], pack_reference_state[15:0]};
            model_req_valid <= 1'b1;
            request_busy <= ~model_req_ready;
            if (model_req_ready) begin
                request_busy <= 1'b0;
            end
            if (model_rsp_valid) begin
                response_valid <= 1'b1;
                response_data <= model_rsp_data;
                age_cnt <= 4'd0;
            end else if (request_busy) begin
                if (age_cnt != 4'hf) age_cnt <= age_cnt + 4'd1;
                if (age_cnt >= 4'd3) response_stale <= 1'b1;
            end
        end else begin
            model_req_valid <= 1'b0;
            request_busy <= 1'b0;
            age_cnt <= 4'd0;
        end
    end
end

endmodule
