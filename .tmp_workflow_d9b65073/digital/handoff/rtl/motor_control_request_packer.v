module motor_control_request_packer (
    input         clk,
    input         reset_n,
    input         launch_req,
    input         busy_i,
    input  [15:0] cfg_sequence_num,
    input  [15:0] cfg_geometry_id,
    input  [31:0] cfg_flow_condition,
    input  [15:0] cfg_timeout_budget,
    input  [15:0] cfg_freshness_limit,
    input  [15:0] cfg_cmd_min,
    input  [15:0] cfg_cmd_max,
    input  [7:0] cfg_policy,
    output reg    request_valid,
    input         request_ready,
    output reg [127:0] request_payload
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        request_valid <= 1'b0;
        request_payload <= 128'h00000000000000000000000000000000;
    end else begin
        if (launch_req && !busy_i && !request_valid) begin
            request_valid <= 1'b1;
            request_payload <= {16'h0000, cfg_policy, cfg_cmd_max, cfg_cmd_min, cfg_freshness_limit, cfg_timeout_budget, cfg_flow_condition, cfg_geometry_id, cfg_sequence_num, 16'h0000};
        end else if (request_valid && request_ready) begin
            request_valid <= 1'b0;
        end
    end
end

endmodule
