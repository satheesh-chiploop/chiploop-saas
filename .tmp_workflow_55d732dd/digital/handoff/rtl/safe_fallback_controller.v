module safe_fallback_controller (
    input clk_rst_n,
    input fallback_enable_i,
    input [31:0] fallback_code_i,
    input [31:0] neutral_code_i,
    input error_i,
    input timeout_i,
    input stale_i,
    input rejected_i,
    input service_busy_i,
    output reg [31:0] safe_cmd_o,
    output reg safe_valid_o,
    output reg fallback_active_o
);
    always @(posedge clk_rst_n or negedge clk_rst_n) begin
        if (!clk_rst_n) begin
            safe_cmd_o <= 32'h00000000;
            safe_valid_o <= 1'b0;
            fallback_active_o <= 1'b1;
        end else begin
            if (error_i || timeout_i || stale_i || rejected_i || service_busy_i || !fallback_enable_i) begin
                safe_cmd_o <= fallback_code_i;
                safe_valid_o <= 1'b1;
                fallback_active_o <= 1'b1;
            end else begin
                safe_cmd_o <= neutral_code_i;
                safe_valid_o <= 1'b1;
                fallback_active_o <= 1'b0;
            end
        end
    end
endmodule
