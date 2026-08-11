module status_telemetry (
    input         clk,
    input         reset_n,
    input         enable,
    input         valid_command_seen,
    input         stale_reject,
    input         timeout_fault,
    input         checksum_fault,
    input         clamp_active,
    input         fallback_active,
    input  [7:0] last_good_sequence,
    output reg [31:0] status_image,
    output reg    status_valid
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        status_image <= 32'd0;
        status_valid <= 1'b0;
    end else begin
        status_image <= {8'b0, 8'd0, last_good_sequence, 1'b0, fallback_active, clamp_active, checksum_fault, timeout_fault, stale_reject, valid_command_seen, enable};
        status_valid <= 1'b1;
    end
end

endmodule
