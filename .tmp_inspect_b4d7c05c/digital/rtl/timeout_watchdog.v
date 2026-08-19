module timeout_watchdog (
    clk,
    reset_n,
    request_issued,
    response_accepted,
    clear_faults,
    timeout_cycles,
    freshness_cycles,
    busy,
    timeout_expired,
    freshness_ok,
    watchdog_active
);
    input clk;
    input reset_n;
    input request_issued;
    input response_accepted;
    input clear_faults;
    input [31:0] timeout_cycles;
    input [31:0] freshness_cycles;
    input busy;
    output timeout_expired;
    output freshness_ok;
    output watchdog_active;

    reg timeout_expired_r;
    reg freshness_ok_r;
    reg watchdog_active_r;
    reg [31:0] timeout_count_r;
    reg [31:0] freshness_count_r;

    assign timeout_expired = timeout_expired_r;
    assign freshness_ok = freshness_ok_r;
    assign watchdog_active = watchdog_active_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            timeout_expired_r <= 1'b0;
            freshness_ok_r <= 1'b0;
            watchdog_active_r <= 1'b0;
            timeout_count_r <= 32'h00000000;
            freshness_count_r <= 32'h00000000;
        end else begin
            if (clear_faults || request_issued || response_accepted) begin
                timeout_expired_r <= 1'b0;
            end
            if (clear_faults || request_issued || response_accepted) begin
                freshness_ok_r <= 1'b0;
            end
            if (request_issued) begin
                watchdog_active_r <= 1'b1;
                timeout_count_r <= 32'h00000000;
                freshness_count_r <= 32'h00000000;
            end else if (busy && watchdog_active_r) begin
                timeout_count_r <= timeout_count_r + 32'h00000001;
                freshness_count_r <= freshness_count_r + 32'h00000001;
                if (timeout_cycles != 32'h00000000 && timeout_count_r >= timeout_cycles) begin
                    timeout_expired_r <= 1'b1;
                end
                if (freshness_cycles == 32'h00000000) begin
                    freshness_ok_r <= 1'b1;
                end else if (freshness_count_r <= freshness_cycles) begin
                    freshness_ok_r <= 1'b1;
                end else begin
                    freshness_ok_r <= 1'b0;
                end
            end else if (response_accepted) begin
                watchdog_active_r <= 1'b0;
                freshness_ok_r <= 1'b1;
                timeout_count_r <= 32'h00000000;
                freshness_count_r <= 32'h00000000;
            end else if (clear_faults) begin
                watchdog_active_r <= 1'b0;
                timeout_count_r <= 32'h00000000;
                freshness_count_r <= 32'h00000000;
            end
        end
    end

endmodule
