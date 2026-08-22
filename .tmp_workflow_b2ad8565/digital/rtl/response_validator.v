module response_validator (
    input         clk,
    input         rst_n,
    input         rsp_valid,
    input  [79:0] rsp_data,
    output        rsp_ready,
    input  [15:0] expected_request_id,
    input  [15:0] cfg_response_age_limit,
    input  [2:0] cfg_mode,
    output reg    validated_response_valid,
    output reg [31:0] validated_response_data,
    output reg    response_reject,
    output reg [3:0] response_reject_code,
    output reg [15:0] response_age_snapshot
);

assign rsp_ready = 1'b1;

wire format_ok;
wire seq_ok;
wire age_ok;
wire status_ok;
wire [31:0] payload;

assign format_ok = (rsp_data[79:72] == 8'hA5);
assign seq_ok = (rsp_data[71:56] == expected_request_id);
assign age_ok = (rsp_data[55:40] <= cfg_response_age_limit);
assign status_ok = (rsp_data[39:37] == 3'b000) & (cfg_mode != 3'b111);
assign payload = rsp_data[31:0];

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        validated_response_valid <= 1'b0;
        validated_response_data <= 32'h00000000;
        response_reject <= 1'b0;
        response_reject_code <= 4'h0;
        response_age_snapshot <= 16'h0000;
    end else begin
        validated_response_valid <= 1'b0;
        response_reject <= 1'b0;
        response_reject_code <= 4'h0;
        if (rsp_valid) begin
            response_age_snapshot <= rsp_data[55:40];
            if (format_ok && seq_ok && age_ok && status_ok) begin
                validated_response_valid <= 1'b1;
                validated_response_data <= payload;
            end else begin
                response_reject <= 1'b1;
                if (!format_ok) response_reject_code <= 4'h1;
                else if (!seq_ok) response_reject_code <= 4'h2;
                else if (!age_ok) response_reject_code <= 4'h3;
                else response_reject_code <= 4'h4;
            end
        end
    end
end

endmodule
