module timeout_monitor (
    input         clk,
    input         reset_n,
    input         enable,
    input         valid_command_seen,
    input         request_pending,
    input         fresh_command_event,
    input  [15:0] timeout_limit_cycles,
    output reg    timeout_fault,
    output reg    wait_active,
    output reg [15:0] timeout_counter
);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        timeout_fault <= 1'b0;
        wait_active <= 1'b0;
        timeout_counter <= 16'd0;
    end else begin
        if (enable && (request_pending || !valid_command_seen || fresh_command_event)) begin
            wait_active <= 1'b1;
            if (fresh_command_event || valid_command_seen) begin
                timeout_counter <= 16'd0;
                timeout_fault <= 1'b0;
                wait_active <= 1'b0;
            end else if (timeout_counter >= timeout_limit_cycles) begin
                timeout_fault <= 1'b1;
            end else begin
                timeout_counter <= timeout_counter + 16'd1;
            end
        end else begin
            wait_active <= 1'b0;
            timeout_counter <= 16'd0;
            timeout_fault <= 1'b0;
        end
    end
end

endmodule
