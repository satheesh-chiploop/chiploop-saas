module adaptive_aero_control_top (
    input              clk,
    input              rst_n,
    input      [7:0] csr_addr,
    input      [63:0] csr_wdata,
    input              csr_wen,
    input              csr_ren,
    output reg [63:0] csr_rdata,
    output reg         csr_ready,
    input              csr_irq_clear,
    output reg         req_valid,
    input              req_ready,
    output reg [63:0] req_data,
    input              resp_valid,
    output reg         resp_ready,
    input      [63:0] resp_data,
    output reg         actuator_valid,
    input              actuator_ready,
    output reg [63:0] actuator_data,
    output reg         fault_irq
);

    localparam [2:0] ST_IDLE       = 3'd0;
    localparam [2:0] ST_ISSUE_REQ   = 3'd1;
    localparam [2:0] ST_WAIT_RESP   = 3'd2;
    localparam [2:0] ST_ACCEPT_RESP = 3'd3;
    localparam [2:0] ST_APPLY_CMD   = 3'd4;
    localparam [2:0] ST_FALLBACK    = 3'd5;
    localparam [2:0] ST_ERROR_HOLD  = 3'd6;

    reg [2:0]  state, next_state;

    reg        enable;
    reg        soft_reset;
    reg [1:0]  mode_select;
    reg [31:0] timeout_cycles;
    reg [31:0] stale_age_limit;
    reg [31:0] seq_seed;
    reg [63:0] actuator_min_limit;
    reg [63:0] actuator_max_limit;
    reg [63:0] fallback_command;

    reg [31:0] timeout_cnt;
    reg [31:0] stale_cnt;
    reg [31:0] invalid_cnt;
    reg [63:0] last_good_sequence;
    reg [63:0] outstanding_sequence;
    reg [31:0] req_age_cnt;
    reg        req_outstanding;
    reg        timeout_latched;
    reg        stale_latched;
    reg        invalid_latched;
    reg        fatal_latched;
    reg        response_match;
    reg        response_valid_ok;
    reg        response_type_ok;
    reg        response_status_ok;
    reg [63:0] response_cmd;
    reg [63:0] clamped_cmd;
    reg [63:0] next_sequence;
    reg [63:0] req_packet;
    reg [63:0] resp_packet;
    reg [63:0] status_reg_read;

    wire [63:0] req_seq_ext;
    wire [63:0] timeout_cycles_ext;
    wire [63:0] stale_age_limit_ext;
    wire [63:0] req_age_ext;
    wire [63:0] resp_seq_ext;

    assign req_seq_ext = outstanding_sequence;
    assign timeout_cycles_ext = {32'b0, timeout_cycles};
    assign stale_age_limit_ext = {32'b0, stale_age_limit};
    assign req_age_ext = {32'b0, req_age_cnt};
    assign resp_seq_ext = resp_data[63:0];

    function [63:0] clamp64;
        input [63:0] val;
        input [63:0] minv;
        input [63:0] maxv;
        begin
            if (val < minv)
                clamp64 = minv;
            else if (val > maxv)
                clamp64 = maxv;
            else
                clamp64 = val;
        end
    endfunction

    always @(*) begin
        next_state = state;

        response_match = 1'b0;
        response_valid_ok = 1'b0;
        response_type_ok = 1'b0;
        response_status_ok = 1'b0;
        response_cmd = fallback_command;
        clamped_cmd = clamp64(response_cmd, actuator_min_limit, actuator_max_limit);
        req_packet = {8'hA1, mode_select, 22'b0, outstanding_sequence[31:0], req_age_cnt[31:0]};
        resp_packet = resp_data;
        status_reg_read = 64'b0;
        next_sequence = outstanding_sequence + 64'd1;

        response_valid_ok = resp_valid;
        response_type_ok = (resp_data[63:56] == 8'hB1);
        response_match = (resp_data[31:0] == outstanding_sequence[31:0]);
        response_status_ok = resp_data[55];

        case (state)
            ST_IDLE: begin
                if (enable && !req_outstanding) begin
                    if (req_ready)
                        next_state = ST_WAIT_RESP;
                    else
                        next_state = ST_ISSUE_REQ;
                end else if (!enable) begin
                    next_state = ST_FALLBACK;
                end else begin
                    next_state = ST_IDLE;
                end
            end

            ST_ISSUE_REQ: begin
                if (req_ready)
                    next_state = ST_WAIT_RESP;
                else
                    next_state = ST_ISSUE_REQ;
            end

            ST_WAIT_RESP: begin
                if (!enable) begin
                    next_state = ST_FALLBACK;
                end else if (resp_valid) begin
                    if (response_valid_ok && response_type_ok && response_match && response_status_ok) begin
                        response_cmd = resp_data;
                        clamped_cmd = clamp64(response_cmd, actuator_min_limit, actuator_max_limit);
                        next_state = ST_ACCEPT_RESP;
                    end else begin
                        next_state = ST_ERROR_HOLD;
                    end
                end else if (timeout_cnt >= timeout_cycles) begin
                    next_state = ST_ERROR_HOLD;
                end else if (req_age_cnt >= stale_age_limit) begin
                    next_state = ST_FALLBACK;
                end else begin
                    next_state = ST_WAIT_RESP;
                end
            end

            ST_ACCEPT_RESP: begin
                if (actuator_ready)
                    next_state = ST_APPLY_CMD;
                else
                    next_state = ST_ACCEPT_RESP;
            end

            ST_APPLY_CMD: begin
                next_state = ST_IDLE;
            end

            ST_FALLBACK: begin
                if (actuator_ready)
                    next_state = ST_ERROR_HOLD;
                else
                    next_state = ST_FALLBACK;
            end

            ST_ERROR_HOLD: begin
                if (enable && !fatal_latched)
                    next_state = ST_IDLE;
                else
                    next_state = ST_ERROR_HOLD;
            end

            default: begin
                next_state = ST_IDLE;
            end
        endcase

        status_reg_read[0] = enable;
        status_reg_read[1] = soft_reset;
        status_reg_read[3:2] = mode_select;
        status_reg_read[4] = req_outstanding;
        status_reg_read[5] = timeout_latched;
        status_reg_read[6] = stale_latched;
        status_reg_read[7] = invalid_latched;
        status_reg_read[8] = fatal_latched;
        status_reg_read[15:9] = 7'b0;
        status_reg_read[31:16] = timeout_cnt[15:0];
        status_reg_read[63:32] = req_age_cnt;
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= ST_IDLE;
            enable <= 1'b0;
            soft_reset <= 1'b0;
            mode_select <= 2'b00;
            timeout_cycles <= 32'd1024;
            stale_age_limit <= 32'd256;
            seq_seed <= 32'd1;
            actuator_min_limit <= 64'd0;
            actuator_max_limit <= 64'd1023;
            fallback_command <= 64'd0;
            timeout_cnt <= 32'd0;
            stale_cnt <= 32'd0;
            invalid_cnt <= 32'd0;
            last_good_sequence <= 64'd0;
            outstanding_sequence <= 64'd0;
            req_age_cnt <= 32'd0;
            req_outstanding <= 1'b0;
            timeout_latched <= 1'b0;
            stale_latched <= 1'b0;
            invalid_latched <= 1'b0;
            fatal_latched <= 1'b0;
            csr_rdata <= 64'd0;
            csr_ready <= 1'b1;
            req_valid <= 1'b0;
            req_data <= 64'd0;
            resp_ready <= 1'b0;
            actuator_valid <= 1'b0;
            actuator_data <= 64'd0;
            fault_irq <= 1'b0;
        end else begin
            state <= next_state;

            csr_ready <= 1'b1;
            csr_rdata <= status_reg_read;

            if (csr_irq_clear) begin
                timeout_latched <= 1'b0;
                stale_latched <= 1'b0;
                invalid_latched <= 1'b0;
                fatal_latched <= 1'b0;
                timeout_cnt <= 32'd0;
                stale_cnt <= 32'd0;
                invalid_cnt <= 32'd0;
            end

            if (csr_wen) begin
                case (csr_addr)
                    8'h00: begin
                        enable <= csr_wdata[0];
                        soft_reset <= csr_wdata[1];
                        mode_select <= csr_wdata[3:2];
                    end
                    8'h04: timeout_cycles <= csr_wdata[31:0];
                    8'h08: stale_age_limit <= csr_wdata[31:0];
                    8'h0C: seq_seed <= csr_wdata[31:0];
                    8'h10: actuator_min_limit <= csr_wdata;
                    8'h14: actuator_max_limit <= csr_wdata;
                    8'h18: fallback_command <= csr_wdata;
                    8'h1C: begin
                        if (csr_wdata[0])
                            timeout_latched <= 1'b0;
                        if (csr_wdata[1])
                            stale_latched <= 1'b0;
                        if (csr_wdata[2])
                            invalid_latched <= 1'b0;
                        if (csr_wdata[3])
                            fatal_latched <= 1'b0;
                    end
                    8'h20: begin
                        if (csr_wdata[0]) begin
                            timeout_cnt <= 32'd0;
                            stale_cnt <= 32'd0;
                            invalid_cnt <= 32'd0;
                        end
                    end
                    8'h24: last_good_sequence <= csr_wdata;
                    default: begin
                    end
                endcase
            end

            if (soft_reset) begin
                state <= ST_IDLE;
                req_outstanding <= 1'b0;
                req_age_cnt <= 32'd0;
                outstanding_sequence <= {32'b0, seq_seed};
                last_good_sequence <= {32'b0, seq_seed};
                timeout_latched <= 1'b0;
                stale_latched <= 1'b0;
                invalid_latched <= 1'b0;
                fatal_latched <= 1'b0;
                req_valid <= 1'b0;
                resp_ready <= 1'b0;
                actuator_valid <= 1'b0;
                actuator_data <= clamp64(fallback_command, actuator_min_limit, actuator_max_limit);
                soft_reset <= 1'b0;
            end else begin
                if (state == ST_IDLE) begin
                    if (enable && !req_outstanding && req_ready) begin
                        req_outstanding <= 1'b1;
                        outstanding_sequence <= next_sequence;
                        req_age_cnt <= 32'd0;
                        req_valid <= 1'b1;
                    end
                end else if (state == ST_ISSUE_REQ) begin
                    req_valid <= 1'b1;
                    if (req_ready) begin
                        req_outstanding <= 1'b1;
                        outstanding_sequence <= next_sequence;
                        req_age_cnt <= 32'd0;
                    end
                end else if (state == ST_WAIT_RESP) begin
                    req_valid <= 1'b0;
                    if (req_outstanding)
                        req_age_cnt <= req_age_cnt + 32'd1;
                    if (resp_valid) begin
                        if (response_valid_ok && response_type_ok && response_match && response_status_ok) begin
                            req_outstanding <= 1'b0;
                            last_good_sequence <= outstanding_sequence;
                            req_age_cnt <= 32'd0;
                            actuator_data <= clamped_cmd;
                        end else begin
                            invalid_cnt <= invalid_cnt + 32'd1;
                            invalid_latched <= 1'b1;
                            fatal_latched <= 1'b1;
                        end
                    end else if (timeout_cnt >= timeout_cycles) begin
                        timeout_latched <= 1'b1;
                        fatal_latched <= 1'b1;
                        timeout_cnt <= timeout_cnt + 32'd1;
                    end else if (req_age_cnt >= stale_age_limit) begin
                        stale_cnt <= stale_cnt + 32'd1;
                        stale_latched <= 1'b1;
                        fatal_latched <= 1'b1;
                    end else begin
                        timeout_cnt <= timeout_cnt + 32'd1;
                    end
                end else if (state == ST_ACCEPT_RESP) begin
                    if (actuator_ready) begin
                        actuator_valid <= 1'b1;
                        actuator_data <= clamped_cmd;
                    end
                end else if (state == ST_APPLY_CMD) begin
                    req_outstanding <= 1'b0;
                    timeout_cnt <= 32'd0;
                    req_age_cnt <= 32'd0;
                end else if (state == ST_FALLBACK) begin
                    actuator_data <= clamp64(fallback_command, actuator_min_limit, actuator_max_limit);
                    if (actuator_ready)
                        req_outstanding <= 1'b0;
                    fatal_latched <= 1'b1;
                end else if (state == ST_ERROR_HOLD) begin
                    actuator_data <= clamp64(fallback_command, actuator_min_limit, actuator_max_limit);
                    fatal_latched <= 1'b1;
                    if (resp_valid && resp_ready) begin
                        req_outstanding <= 1'b0;
                    end
                end
            end

            fault_irq <= timeout_latched | stale_latched | invalid_latched | fatal_latched;
        end
    end

endmodule
