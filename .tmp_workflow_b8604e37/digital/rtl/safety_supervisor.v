module safety_supervisor (
    input clk,
    input rst_n,
    input cfg_enable,
    input [1:0] cfg_mode_sel,
    input cfg_fault_clear,
    input fault_latched_clear,
    input req_accept,
    input req_reject,
    input req_fault,
    input req_stale,
    input req_timeout,
    input rsp_accept,
    input rsp_reject,
    input rsp_fresh_ok,
    input heartbeat_seen,
    output reg [1:0] status_mode,
    output reg fault_latched,
    output reg timeout_status,
    output reg stale_status,
    output reg fallback_entry,
    output reg armed,
    output reg active,
    output reg wait_response
);

localparam ST_IDLE = 2'd0;
localparam ST_ARMED = 2'd1;
localparam ST_ACTIVE = 2'd2;
localparam ST_WAIT_RESPONSE = 2'd3;

reg [1:0] state;
reg fault_clear_seen;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= ST_IDLE;
        status_mode <= ST_IDLE;
        fault_latched <= 1'b0;
        timeout_status <= 1'b0;
        stale_status <= 1'b0;
        fallback_entry <= 1'b0;
        armed <= 1'b0;
        active <= 1'b0;
        wait_response <= 1'b0;
        fault_clear_seen <= 1'b0;
    end else begin
        fallback_entry <= 1'b0;
        fault_clear_seen <= 1'b0;
        if (cfg_fault_clear || fault_latched_clear) fault_clear_seen <= 1'b1;
        if (!cfg_enable) begin
            state <= ST_IDLE;
            armed <= 1'b0;
            active <= 1'b0;
            wait_response <= 1'b0;
            fallback_entry <= 1'b1;
        end else if (fault_latched && !fault_clear_seen) begin
            state <= ST_IDLE;
            armed <= 1'b0;
            active <= 1'b0;
            wait_response <= 1'b0;
            fallback_entry <= 1'b1;
        end else begin
            if (fault_clear_seen) fault_latched <= 1'b0;
            if (req_fault || req_timeout || req_stale || rsp_reject || !heartbeat_seen) begin
                fault_latched <= fault_latched | req_fault;
                timeout_status <= timeout_status | req_timeout | (!heartbeat_seen);
                stale_status <= stale_status | req_stale;
                state <= ST_IDLE;
                armed <= 1'b0;
                active <= 1'b0;
                wait_response <= 1'b0;
                fallback_entry <= 1'b1;
            end else begin
                case (state)
                    ST_IDLE: begin
                        armed <= 1'b1;
                        active <= 1'b0;
                        wait_response <= 1'b0;
                        if (req_accept) state <= ST_WAIT_RESPONSE;
                        else if (cfg_mode_sel != 2'b00) state <= ST_ARMED;
                    end
                    ST_ARMED: begin
                        armed <= 1'b1;
                        active <= 1'b0;
                        wait_response <= 1'b0;
                        if (req_accept) state <= ST_WAIT_RESPONSE;
                        else if (!cfg_enable) state <= ST_IDLE;
                        else if (cfg_mode_sel == 2'b11) state <= ST_ACTIVE;
                    end
                    ST_WAIT_RESPONSE: begin
                        armed <= 1'b1;
                        active <= 1'b0;
                        wait_response <= 1'b1;
                        if (rsp_accept && rsp_fresh_ok) state <= ST_ACTIVE;
                        else if (req_reject) begin
                            state <= ST_ARMED;
                        end
                    end
                    default: begin
                        armed <= 1'b0;
                        active <= 1'b0;
                        wait_response <= 1'b0;
                        state <= ST_IDLE;
                    end
                endcase
            end
        end
        status_mode <= state;
    end
end

endmodule
