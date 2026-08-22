module safety_monitor (
    input         clk,
    input         rst_n,
    input         cfg_enable,
    input  [15:0] cfg_timeout_threshold,
    input         request_outstanding,
    input         response_accepted,
    input         response_reject,
    input         fault_clear,
    output reg    safe_fallback,
    output reg    fault_latched,
    output reg [7:0] fault_cause,
    output reg [15:0] timeout_counter_snapshot,
    output reg    fault_irq
);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        safe_fallback <= 1'b1;
        fault_latched <= 1'b0;
        fault_cause <= 8'h00;
        timeout_counter_snapshot <= 16'h0000;
        fault_irq <= 1'b0;
    end else begin
        if (fault_clear) begin
            fault_latched <= 1'b0;
            fault_cause <= 8'h00;
        end
        if (!cfg_enable) begin
            safe_fallback <= 1'b1;
        end else if (request_outstanding) begin
            safe_fallback <= 1'b0;
        end
        if (response_accepted) begin
            timeout_counter_snapshot <= 16'h0000;
            safe_fallback <= 1'b0;
        end else if (request_outstanding) begin
            if (timeout_counter_snapshot < cfg_timeout_threshold) begin
                timeout_counter_snapshot <= timeout_counter_snapshot + 16'h0001;
            end else begin
                fault_latched <= 1'b1;
                fault_cause <= 8'h01;
                safe_fallback <= 1'b1;
            end
        end else begin
            timeout_counter_snapshot <= 16'h0000;
        end
        if (response_reject) begin
            fault_latched <= 1'b1;
            fault_cause <= 8'h02;
            safe_fallback <= 1'b1;
        end
        fault_irq <= fault_latched;
    end
end

endmodule
