module request_framing_engine (
    input         clk,
    input         rst_n,
    input         cfg_enable,
    input  [2:0] cfg_mode,
    input  [15:0] cfg_request_seq_seed,
    input         request_launch,
    input         request_ack,
    output reg    request_busy,
    output reg [15:0] request_id,
    output reg    cmd_valid,
    output reg [79:0] cmd_data,
    input         cmd_ready
);

reg [1:0] state;
reg [79:0] cmd_hold;
reg pending_launch;

localparam ST_IDLE = 2'd0;
localparam ST_WAIT_ACCEPT = 2'd1;
localparam ST_OUTSTANDING = 2'd2;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= ST_IDLE;
        request_busy <= 1'b0;
        request_id <= 16'h0000;
        cmd_valid <= 1'b0;
        cmd_data <= 80'h00000000000000000000;
        cmd_hold <= 80'h00000000000000000000;
        pending_launch <= 1'b0;
    end else begin
        if (request_ack) begin
            request_busy <= 1'b0;
            state <= ST_IDLE;
        end
        case (state)
            ST_IDLE: begin
                cmd_valid <= 1'b0;
                if (cfg_enable && request_launch) begin
                    request_id <= (request_id == 16'h0000) ? cfg_request_seq_seed : (request_id + 16'h0001);
                    cmd_hold <= {request_id, cfg_mode, 61'h00000000000000000};
                    cmd_data <= {request_id, cfg_mode, 61'h00000000000000000};
                    cmd_valid <= 1'b1;
                    request_busy <= 1'b1;
                    state <= ST_WAIT_ACCEPT;
                end
            end
            ST_WAIT_ACCEPT: begin
                cmd_valid <= 1'b1;
                cmd_data <= cmd_hold;
                request_busy <= 1'b1;
                if (cmd_ready) begin
                    cmd_valid <= 1'b0;
                    state <= ST_OUTSTANDING;
                end
            end
            ST_OUTSTANDING: begin
                cmd_valid <= 1'b0;
                request_busy <= 1'b1;
                if (!cfg_enable) begin
                    request_busy <= 1'b0;
                    state <= ST_IDLE;
                end
            end
            default: begin
                state <= ST_IDLE;
                request_busy <= 1'b0;
                cmd_valid <= 1'b0;
            end
        endcase
    end
end

endmodule
