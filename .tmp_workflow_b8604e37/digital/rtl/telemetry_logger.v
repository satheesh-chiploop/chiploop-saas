module telemetry_logger (
    input clk,
    input rst_n,
    input req_accept,
    input req_reject,
    input req_timeout,
    input req_stale,
    input fallback_entry,
    input [15:0] last_valid_seq,
    output reg [15:0] telemetry_accepted_packets,
    output reg [15:0] telemetry_rejected_packets,
    output reg [15:0] telemetry_timeout_events,
    output reg [15:0] telemetry_stale_events,
    output reg [15:0] telemetry_fallback_entries,
    output reg [15:0] telemetry_last_valid_seq
);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        telemetry_accepted_packets <= 16'h0000;
        telemetry_rejected_packets <= 16'h0000;
        telemetry_timeout_events <= 16'h0000;
        telemetry_stale_events <= 16'h0000;
        telemetry_fallback_entries <= 16'h0000;
        telemetry_last_valid_seq <= 16'h0000;
    end else begin
        if (req_accept) telemetry_accepted_packets <= telemetry_accepted_packets + 16'h0001;
        if (req_reject) telemetry_rejected_packets <= telemetry_rejected_packets + 16'h0001;
        if (req_timeout) telemetry_timeout_events <= telemetry_timeout_events + 16'h0001;
        if (req_stale) telemetry_stale_events <= telemetry_stale_events + 16'h0001;
        if (fallback_entry) telemetry_fallback_entries <= telemetry_fallback_entries + 16'h0001;
        telemetry_last_valid_seq <= last_valid_seq;
    end
end

endmodule
