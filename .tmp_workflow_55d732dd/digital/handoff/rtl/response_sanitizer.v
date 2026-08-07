module response_sanitizer (
    input clk_rst_n,
    input resp_valid_i,
    input [15:0] resp_request_id_i,
    input [7:0] resp_status_i,
    input [31:0] resp_actuator_cmd_i,
    input resp_fallback_i,
    input [15:0] latest_request_id_i,
    input timeout_expired_i,
    input service_error_i,
    input [31:0] clamp_min_i,
    input [31:0] clamp_max_i,
    output reg sanitized_valid_o,
    output reg [31:0] sanitized_cmd_o,
    output reg accepted_o,
    output reg stale_o,
    output reg timeout_o,
    output reg fallback_o,
    output reg error_o
);
    reg [31:0] clamp_lo_r;
    reg [31:0] clamp_hi_r;

    always @(posedge clk_rst_n or negedge clk_rst_n) begin
        if (!clk_rst_n) begin
            sanitized_valid_o <= 1'b0;
            sanitized_cmd_o <= 32'h00000000;
            accepted_o <= 1'b0;
            stale_o <= 1'b0;
            timeout_o <= 1'b0;
            fallback_o <= 1'b0;
            error_o <= 1'b0;
            clamp_lo_r <= 32'h00000000;
            clamp_hi_r <= 32'hFFFFFFFF;
        end else begin
            sanitized_valid_o <= 1'b0;
            accepted_o <= 1'b0;
            stale_o <= 1'b0;
            timeout_o <= timeout_expired_i;
            fallback_o <= resp_fallback_i;
            error_o <= service_error_i;
            if (clamp_min_i <= clamp_max_i) begin
                clamp_lo_r <= clamp_min_i;
                clamp_hi_r <= clamp_max_i;
            end else begin
                clamp_lo_r <= clamp_max_i;
                clamp_hi_r <= clamp_min_i;
            end
            if (resp_valid_i && !timeout_expired_i && !service_error_i) begin
                if (resp_request_id_i == latest_request_id_i) begin
                    accepted_o <= 1'b1;
                    sanitized_valid_o <= 1'b1;
                    if (resp_actuator_cmd_i < clamp_lo_r)
                        sanitized_cmd_o <= clamp_lo_r;
                    else if (resp_actuator_cmd_i > clamp_hi_r)
                        sanitized_cmd_o <= clamp_hi_r;
                    else
                        sanitized_cmd_o <= resp_actuator_cmd_i;
                end else begin
                    stale_o <= 1'b1;
                end
            end
            if (resp_status_i[0])
                error_o <= 1'b1;
        end
    end
endmodule
