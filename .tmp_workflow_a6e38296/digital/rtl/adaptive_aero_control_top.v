module adaptive_aero_control_top (
    input         clk,
    input         rst_n,
    input         req_valid,
    output        req_ready,
    input  [127:0] req_data,
    input         resp_valid,
    output        resp_ready,
    input  [127:0] resp_data,
    output        model_req_valid,
    input         model_req_ready,
    output [127:0] model_req_data,
    input         model_resp_valid,
    output        model_resp_ready,
    input  [127:0] model_resp_data,
    output [31:0] act_cmd,
    output        act_valid,
    input         act_ready,
    output reg    status_busy,
    output reg    status_accepted,
    output reg    status_stale_rejected,
    output reg    status_timeout_fault,
    output reg    status_envelope_violation,
    output reg    status_malformed_request,
    output reg    status_fallback_active,
    output reg    status_clamped_output,
    output reg    status_irq,
    input  [15:0] cfg_min_velocity,
    input  [15:0] cfg_max_velocity,
    input  [15:0] cfg_freshness_limit,
    input  [15:0] cfg_timeout_limit,
    input  [31:0] cfg_min_cmd,
    input  [31:0] cfg_max_cmd,
    input         cfg_rate_limit_enable,
    input  [31:0] cfg_rate_limit_step,
    input         cfg_last_known_good_enable,
    input  [31:0] cfg_default_safe_cmd,
    input         cfg_irq_enable
);

    localparam ST_IDLE     = 3'd0;
    localparam ST_WAIT_REQ = 3'd1;
    localparam ST_WAIT_DEC = 3'd2;
    localparam ST_EMIT_ACT  = 3'd3;
    localparam ST_FALLBACK  = 3'd4;

    localparam SRC_NONE  = 2'd0;
    localparam SRC_MODEL = 2'd1;
    localparam SRC_HOST  = 2'd2;
    localparam SRC_SAFE  = 2'd3;

    reg [2:0]  state, state_n;
    reg [2:0]  queue_state, queue_state_n;
    reg [127:0] req_fifo0, req_fifo1;
    reg [127:0] resp_fifo0, resp_fifo1;
    reg [1:0]   req_wr_ptr, req_rd_ptr, req_count;
    reg [1:0]   resp_wr_ptr, resp_rd_ptr, resp_count;
    reg [15:0]  timer_cnt;
    reg [15:0]  fresh_cnt;
    reg [15:0]  last_seq;
    reg [15:0]  last_ts;
    reg [31:0]  last_good_cmd;
    reg [31:0] emitted_cmd;
    reg [31:0]  selected_cmd;
    reg [31:0]  next_cmd;
    reg [31:0]  safe_cmd;
    reg [31:0]  clamped_cmd;
    reg [31:0]  rate_limited_cmd;
    reg [31:0]  parsed_target;
    reg [15:0]  parsed_velocity;
    reg [15:0]  parsed_seq;
    reg [15:0]  parsed_ts;
    reg [7:0]   parsed_opcode;
    reg [15:0]  parsed_geom;
    reg [15:0]  parsed_flow;
    reg [15:0]  local_time;
    reg [1:0]   decision_source;
    reg         have_req;
    reg         have_resp;
    reg         req_accept;
    reg         resp_accept;
    reg         req_malformed;
    reg         req_stale;
    reg         req_env_viol;
    reg         resp_malformed;
    reg         resp_seq_mismatch;
    reg         resp_ts_mismatch;
    reg         timeout_hit;
    reg         clamped_hit;
    reg         rate_hit;
    reg         irq_pulse;
    reg [127:0] req_data_next;
    reg [127:0] resp_data_next;

    wire req_full;
    wire resp_full;
    wire req_empty;
    wire resp_empty;
    wire fresh_ok;
    wire env_ok;
    wire seq_ok;
    wire ts_ok;
    wire timeout_expired;
    wire rate_enable;
    wire lkg_enable;
    wire irq_enable;

    assign req_full = (req_count == 2'd2);
    assign resp_full = (resp_count == 2'd2);
    assign req_empty = (req_count == 2'd0);
    assign resp_empty = (resp_count == 2'd0);
    assign fresh_ok = (fresh_cnt <= cfg_freshness_limit);
    assign env_ok = (parsed_velocity >= cfg_min_velocity) && (parsed_velocity <= cfg_max_velocity);
    assign seq_ok = (parsed_seq == last_seq);
    assign ts_ok = (parsed_ts <= local_time) && ((local_time - parsed_ts) <= cfg_freshness_limit);
    assign timeout_expired = (timer_cnt >= cfg_timeout_limit) && (state == ST_WAIT_DEC);
    assign rate_enable = cfg_rate_limit_enable;
    assign lkg_enable = cfg_last_known_good_enable;
    assign irq_enable = cfg_irq_enable;

    assign req_ready = (!req_full) && (state != ST_FALLBACK);
    assign resp_ready = (!resp_full);
    assign model_req_valid = (state == ST_WAIT_DEC) && have_req && !timeout_expired;
    assign model_req_data = req_fifo0;
    assign model_resp_ready = 1'b1;

    assign act_cmd = emitted_cmd;
    assign act_valid = (state == ST_EMIT_ACT) || (state == ST_FALLBACK);

    always @(*) begin
        state_n = state;
        queue_state_n = queue_state;
        have_req = 1'b0;
        have_resp = 1'b0;
        req_accept = 1'b0;
        resp_accept = 1'b0;
        req_malformed = 1'b0;
        req_stale = 1'b0;
        req_env_viol = 1'b0;
        resp_malformed = 1'b0;
        resp_seq_mismatch = 1'b0;
        resp_ts_mismatch = 1'b0;
        timeout_hit = 1'b0;
        clamped_hit = 1'b0;
        rate_hit = 1'b0;
        irq_pulse = 1'b0;
        parsed_opcode = req_data[127:120];
        parsed_geom = req_data[119:104];
        parsed_flow = req_data[103:88];
        parsed_velocity = req_data[87:72];
        parsed_seq = req_data[71:56];
        parsed_ts = req_data[55:40];
        parsed_target = {req_data[39:8]};
        local_time = fresh_cnt;
        safe_cmd = cfg_default_safe_cmd;
        selected_cmd = emitted_cmd;
        next_cmd = emitted_cmd;
        decision_source = SRC_NONE;
        req_data_next = req_data;
        resp_data_next = resp_data;

        if (req_valid && req_ready) begin
            req_accept = 1'b1;
            have_req = 1'b1;
            if ((parsed_opcode == 8'h00) || (parsed_opcode == 8'hFF)) begin
                req_malformed = 1'b1;
            end
            if (!env_ok) begin
                req_env_viol = 1'b1;
            end
            if (!ts_ok) begin
                req_stale = 1'b1;
            end
            if (parsed_seq < last_seq) begin
                req_malformed = 1'b1;
            end
            if (req_malformed || req_env_viol || req_stale) begin
                state_n = ST_FALLBACK;
                if (irq_enable) irq_pulse = 1'b1;
            end else begin
                state_n = ST_WAIT_DEC;
            end
        end else if (resp_valid && resp_ready) begin
            resp_accept = 1'b1;
            have_resp = 1'b1;
            resp_seq_mismatch = (resp_data[71:56] != last_seq);
            resp_ts_mismatch = (resp_data[55:40] != last_ts);
            if ((resp_data[127:120] == 8'h00) || resp_seq_mismatch || resp_ts_mismatch) begin
                resp_malformed = 1'b1;
            end
            if (resp_malformed) begin
                state_n = ST_FALLBACK;
                if (irq_enable) irq_pulse = 1'b1;
            end else begin
                state_n = ST_EMIT_ACT;
                selected_cmd = resp_data[39:8];
                decision_source = SRC_MODEL;
            end
        end else begin
            if (timeout_expired) begin
                timeout_hit = 1'b1;
                state_n = ST_FALLBACK;
                if (irq_enable) irq_pulse = 1'b1;
            end else if ((state == ST_WAIT_DEC) && model_resp_valid) begin
                resp_malformed = (model_resp_data[127:120] == 8'h00);
                resp_seq_mismatch = (model_resp_data[71:56] != last_seq);
                resp_ts_mismatch = (model_resp_data[55:40] != last_ts);
                if (resp_malformed || resp_seq_mismatch || resp_ts_mismatch) begin
                    state_n = ST_FALLBACK;
                    if (irq_enable) irq_pulse = 1'b1;
                end else begin
                    state_n = ST_EMIT_ACT;
                    selected_cmd = model_resp_data[39:8];
                    decision_source = SRC_MODEL;
                end
            end
        end

        if (selected_cmd < cfg_min_cmd) begin
            clamped_cmd = cfg_min_cmd;
            clamped_hit = 1'b1;
        end else if (selected_cmd > cfg_max_cmd) begin
            clamped_cmd = cfg_max_cmd;
            clamped_hit = 1'b1;
        end else begin
            clamped_cmd = selected_cmd;
        end

        if (rate_enable) begin
            if (clamped_cmd > (last_good_cmd + cfg_rate_limit_step)) begin
                rate_limited_cmd = last_good_cmd + cfg_rate_limit_step;
                rate_hit = 1'b1;
            end else if (clamped_cmd + cfg_rate_limit_step < last_good_cmd) begin
                rate_limited_cmd = last_good_cmd - cfg_rate_limit_step;
                rate_hit = 1'b1;
            end else begin
                rate_limited_cmd = clamped_cmd;
            end
        end else begin
            rate_limited_cmd = clamped_cmd;
        end

        if (state == ST_FALLBACK) begin
            next_cmd = safe_cmd;
            decision_source = SRC_SAFE;
        end else if (state == ST_EMIT_ACT) begin
            next_cmd = rate_limited_cmd;
        end else if (state == ST_WAIT_DEC) begin
            next_cmd = emitted_cmd;
        end else begin
            next_cmd = emitted_cmd;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= ST_IDLE;
            queue_state <= 3'd0;
            req_fifo0 <= 128'd0;
            req_fifo1 <= 128'd0;
            resp_fifo0 <= 128'd0;
            resp_fifo1 <= 128'd0;
            req_wr_ptr <= 2'd0;
            req_rd_ptr <= 2'd0;
            req_count <= 2'd0;
            resp_wr_ptr <= 2'd0;
            resp_rd_ptr <= 2'd0;
            resp_count <= 2'd0;
            timer_cnt <= 16'd0;
            fresh_cnt <= 16'd0;
            last_seq <= 16'd0;
            last_ts <= 16'd0;
            last_good_cmd <= 32'd0;
            emitted_cmd <= 32'd0;
            status_busy <= 1'b0;
            status_accepted <= 1'b0;
            status_stale_rejected <= 1'b0;
            status_timeout_fault <= 1'b0;
            status_envelope_violation <= 1'b0;
            status_malformed_request <= 1'b0;
            status_fallback_active <= 1'b1;
            status_clamped_output <= 1'b0;
            status_irq <= 1'b0;
        end else begin
            state <= state_n;
            fresh_cnt <= fresh_cnt + 16'd1;
            status_accepted <= 1'b0;
            status_stale_rejected <= 1'b0;
            status_timeout_fault <= 1'b0;
            status_envelope_violation <= 1'b0;
            status_malformed_request <= 1'b0;
            status_clamped_output <= 1'b0;
            status_irq <= 1'b0;
            status_busy <= (state_n != ST_IDLE);

            if (req_valid && req_ready) begin
                req_fifo0 <= req_data;
                req_wr_ptr <= req_wr_ptr + 2'd1;
                req_count <= req_count + 2'd1;
                status_accepted <= (!req_malformed && !req_env_viol && !req_stale);
                status_malformed_request <= req_malformed;
                status_envelope_violation <= req_env_viol;
                status_stale_rejected <= req_stale;
                if (!req_malformed && !req_env_viol && !req_stale) begin
                    last_seq <= parsed_seq;
                    last_ts <= parsed_ts;
                    timer_cnt <= 16'd0;
                end
            end

            if (resp_valid && resp_ready) begin
                resp_fifo0 <= resp_data;
                resp_wr_ptr <= resp_wr_ptr + 2'd1;
                resp_count <= resp_count + 2'd1;
                status_malformed_request <= resp_malformed;
                if (resp_malformed) begin
                    status_irq <= irq_pulse;
                end
            end

            if (state == ST_WAIT_DEC) begin
                if (timeout_expired) begin
                    status_timeout_fault <= 1'b1;
                    status_fallback_active <= 1'b1;
                    emitted_cmd <= cfg_default_safe_cmd;
                    last_good_cmd <= cfg_default_safe_cmd;
                    timer_cnt <= 16'd0;
                    status_irq <= irq_pulse;
                end else if (model_resp_valid && model_resp_ready) begin
                    emitted_cmd <= next_cmd;
                    last_good_cmd <= next_cmd;
                    status_clamped_output <= clamped_hit | rate_hit;
                    status_fallback_active <= 1'b0;
                end
            end else if (state == ST_EMIT_ACT) begin
                emitted_cmd <= next_cmd;
                last_good_cmd <= next_cmd;
                status_clamped_output <= clamped_hit | rate_hit;
                status_fallback_active <= 1'b0;
            end else if (state == ST_FALLBACK) begin
                emitted_cmd <= cfg_default_safe_cmd;
                last_good_cmd <= cfg_default_safe_cmd;
                status_fallback_active <= 1'b1;
                status_clamped_output <= 1'b0;
                status_irq <= irq_pulse;
            end

            if (act_valid && act_ready) begin
                if (state == ST_EMIT_ACT || state == ST_FALLBACK) begin
                    timer_cnt <= 16'd0;
                end
            end else if (state == ST_WAIT_DEC) begin
                timer_cnt <= timer_cnt + 16'd1;
            end
        end
    end

endmodule
