module adaptive_aero_control_top (
    clk,
    rst_n,
    cfg_valid,
    cfg_write,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    cfg_ready,
    veh_speed_mps,
    model_req_valid,
    model_req_ready,
    model_req_data,
    model_rsp_valid,
    model_rsp_ready,
    model_rsp_data,
    aero_actuator_valid,
    aero_actuator_cmd,
    status_irq
);
    input clk;
    input rst_n;
    input cfg_valid;
    input cfg_write;
    input [7:0] cfg_addr;
    input [31:0] cfg_wdata;
    output [31:0] cfg_rdata;
    output cfg_ready;
    input [31:0] veh_speed_mps;
    output model_req_valid;
    input model_req_ready;
    output [127:0] model_req_data;
    input model_rsp_valid;
    output model_rsp_ready;
    input [127:0] model_rsp_data;
    output aero_actuator_valid;
    output [31:0] aero_actuator_cmd;
    output status_irq;

    localparam [7:0] ADDR_CTRL         = 8'h00;
    localparam [7:0] ADDR_TIMEOUT_CFG  = 8'h04;
    localparam [7:0] ADDR_CLAMP_MIN    = 8'h08;
    localparam [7:0] ADDR_CLAMP_MAX    = 8'h0C;
    localparam [7:0] ADDR_RATE_LIMIT   = 8'h10;
    localparam [7:0] ADDR_SEQ_SEED     = 8'h14;
    localparam [7:0] ADDR_STATUS       = 8'h18;
    localparam [7:0] ADDR_COUNTER_REQ  = 8'h1C;
    localparam [7:0] ADDR_COUNTER_RSP_OK   = 8'h20;
    localparam [7:0] ADDR_COUNTER_RSP_REJ   = 8'h24;
    localparam [7:0] ADDR_COUNTER_TIMEOUT   = 8'h28;
    localparam [7:0] ADDR_COUNTER_STALE     = 8'h2C;
    localparam [7:0] ADDR_COUNTER_FAULT     = 8'h30;
    localparam [7:0] ADDR_RSP_LAST     = 8'h34;
    localparam [7:0] ADDR_REQ_LAST     = 8'h38;

    localparam [1:0] ST_IDLE      = 2'd0;
    localparam [1:0] ST_WAIT_REQ  = 2'd1;
    localparam [1:0] ST_BUSY      = 2'd2;
    localparam [1:0] ST_FAILSAFE  = 2'd3;

    reg [7:0] ctrl_reg;
    reg [31:0] timeout_cfg_reg;
    reg [31:0] clamp_min_reg;
    reg [31:0] clamp_max_reg;
    reg [31:0] rate_limit_reg;
    reg [31:0] seq_seed_reg;

    reg [31:0] req_counter;
    reg [31:0] rsp_ok_counter;
    reg [31:0] rsp_rej_counter;
    reg [31:0] timeout_counter;
    reg [31:0] stale_counter;
    reg [31:0] fault_counter;

    reg [7:0] status_reg;
    reg [31:0] rsp_last_reg;
    reg [31:0] req_last_reg;

    reg [1:0] state;
    reg [15:0] seq_counter;
    reg [15:0] outstanding_seq;
    reg outstanding_valid;
    reg [31:0] outstanding_launch;
    reg [31:0] cycle_count;
    reg [31:0] timeout_watchdog;
    reg [31:0] speed_sync;
    reg [31:0] final_cmd_reg;
    reg [31:0] last_cmd_reg;
    reg req_pending;
    reg req_valid_reg;
    reg rsp_ready_reg;
    reg actuator_valid_reg;
    reg irq_reg;

    reg cfg_ready_r;
    reg [31:0] cfg_rdata_r;
    reg [127:0] req_data_reg;
    reg [127:0] rsp_data_q;

    wire enable;
    wire [2:0] mode;
    wire clear_sticky;
    wire update_on_same;
    wire fallback_enable;
    wire irq_enable;
    wire timeout_expired_now;
    wire out_of_range_now;
    wire speed_in_range;
    wire outstanding_active;
    wire req_issue_allowed;
    wire req_launch_fire;
    wire rsp_valid_match;
    wire rsp_fresh;
    wire rsp_status_ok;
    wire rsp_good;
    wire [31:0] fallback_cmd;
    wire [31:0] surrogate_cmd;
    wire [31:0] safe_cmd_preclamp;
    wire [31:0] clamped_cmd;
    wire rate_limit_enable;
    wire [15:0] rate_limit_step;
    wire [31:0] rate_diff_abs;
    wire [31:0] rate_limited_cmd;
    wire [31:0] current_speed;
    wire [7:0] req_flags;
    wire [7:0] rsp_status_sum;
    wire [7:0] rsp_age_sum;
    wire [31:0] timeout_thresh;
    wire [31:0] stale_thresh;
    wire [31:0] timeout_watchdog_next;
    wire [31:0] cycle_count_next;
    wire [15:0] seq_next;
    wire [31:0] speed_encoded;
    wire [31:0] req_speed_scalar;
    wire [31:0] req_data_word0;
    wire [31:0] req_data_word1;
    wire [31:0] req_data_word2;
    wire [31:0] req_data_word3;
    wire [31:0] rsp_seq_word;
    wire [31:0] rsp_meta_word;
    wire [31:0] rsp_cmd_word;
    wire [31:0] rsp_age_word;
    wire [31:0] rsp_age_calc;

    assign cfg_ready = cfg_ready_r;
    assign cfg_rdata = cfg_rdata_r;
    assign model_req_valid = req_valid_reg;
    assign model_req_data = req_data_reg;
    assign model_rsp_ready = rsp_ready_reg;
    assign aero_actuator_valid = actuator_valid_reg;
    assign aero_actuator_cmd = final_cmd_reg;
    assign status_irq = irq_reg;

    assign enable = ctrl_reg[0];
    assign mode = ctrl_reg[3:1];
    assign clear_sticky = ctrl_reg[4];
    assign update_on_same = ctrl_reg[5];
    assign fallback_enable = ctrl_reg[6];
    assign irq_enable = ctrl_reg[7];

    assign timeout_thresh = timeout_cfg_reg[15:0];
    assign stale_thresh = timeout_cfg_reg[31:16];
    assign rate_limit_step = rate_limit_reg[15:0];
    assign rate_limit_enable = rate_limit_reg[16];

    assign speed_in_range = (veh_speed_mps >= 32'd20) && (veh_speed_mps <= 32'd55);
    assign out_of_range_now = ~speed_in_range;
    assign current_speed = veh_speed_mps;
    assign speed_encoded = current_speed;

    assign outstanding_active = outstanding_valid;
    assign req_issue_allowed = enable && speed_in_range && !outstanding_active;
    assign timeout_expired_now = outstanding_active && (timeout_watchdog >= timeout_thresh) && (timeout_thresh != 32'd0);

    assign req_launch_fire = req_valid_reg && model_req_ready;
    assign rsp_valid_match = model_rsp_valid && outstanding_active && (model_rsp_data[15:0] == outstanding_seq);
    assign rsp_fresh = outstanding_active && ((cycle_count - outstanding_launch) <= stale_thresh);
    assign rsp_status_ok = (model_rsp_data[23:16] == 8'h00);
    assign rsp_good = rsp_valid_match && rsp_fresh && rsp_status_ok && !timeout_expired_now;

    assign surrogate_cmd = model_rsp_data[31:0];
    assign fallback_cmd = {16'd0, seq_counter};
    assign safe_cmd_preclamp = (enable && speed_in_range && rsp_good) ? surrogate_cmd :
                               ((enable && fallback_enable) ? fallback_cmd : 32'd0);

    assign req_speed_scalar = current_speed;
    assign req_data_word0 = {seq_counter, mode, ctrl_reg, 8'hA5};
    assign req_data_word1 = req_speed_scalar;
    assign req_data_word2 = {timeout_cfg_reg[15:0], clamp_min_reg[15:0]};
    assign req_data_word3 = {clamp_max_reg[15:0], rate_limit_reg[15:0]};
    assign req_flags = {enable, fallback_enable, irq_enable, update_on_same, speed_in_range, outstanding_active, 2'b00};

    assign rsp_seq_word = {16'd0, outstanding_seq};
    assign rsp_meta_word = {16'd0, rsp_status_sum, rsp_age_sum};
    assign rsp_cmd_word = model_rsp_data[31:0];
    assign rsp_age_calc = cycle_count - outstanding_launch;
    assign rsp_age_sum = (rsp_age_calc > 32'd255) ? 8'hFF : rsp_age_calc[7:0];
    assign rsp_age_word = {24'd0, rsp_age_sum};

    assign rsp_status_sum = {model_rsp_valid, rsp_good, rsp_valid_match, rsp_fresh, rsp_status_ok, timeout_expired_now, out_of_range_now, outstanding_active};

    assign clamped_cmd = (safe_cmd_preclamp < clamp_min_reg) ? clamp_min_reg :
                         (safe_cmd_preclamp > clamp_max_reg) ? clamp_max_reg :
                         safe_cmd_preclamp;

    assign rate_diff_abs = (clamped_cmd >= last_cmd_reg) ? (clamped_cmd - last_cmd_reg) : (last_cmd_reg - clamped_cmd);
    assign rate_limited_cmd = (rate_limit_enable && (rate_diff_abs > {16'd0, rate_limit_step})) ?
                              ((clamped_cmd >= last_cmd_reg) ? (last_cmd_reg + {16'd0, rate_limit_step}) :
                                                               (last_cmd_reg - {16'd0, rate_limit_step})) :
                              clamped_cmd;

    always @(*) begin
        cfg_ready_r = 1'b1;
        cfg_rdata_r = 32'd0;
        case (cfg_addr)
            ADDR_CTRL: cfg_rdata_r = {24'd0, ctrl_reg};
            ADDR_TIMEOUT_CFG: cfg_rdata_r = timeout_cfg_reg;
            ADDR_CLAMP_MIN: cfg_rdata_r = clamp_min_reg;
            ADDR_CLAMP_MAX: cfg_rdata_r = clamp_max_reg;
            ADDR_RATE_LIMIT: cfg_rdata_r = rate_limit_reg;
            ADDR_SEQ_SEED: cfg_rdata_r = seq_seed_reg;
            ADDR_STATUS: cfg_rdata_r = {24'd0, status_reg};
            ADDR_COUNTER_REQ: cfg_rdata_r = req_counter;
            ADDR_COUNTER_RSP_OK: cfg_rdata_r = rsp_ok_counter;
            ADDR_COUNTER_RSP_REJ: cfg_rdata_r = rsp_rej_counter;
            ADDR_COUNTER_TIMEOUT: cfg_rdata_r = timeout_counter;
            ADDR_COUNTER_STALE: cfg_rdata_r = stale_counter;
            ADDR_COUNTER_FAULT: cfg_rdata_r = fault_counter;
            ADDR_RSP_LAST: cfg_rdata_r = rsp_last_reg;
            ADDR_REQ_LAST: cfg_rdata_r = req_last_reg;
            default: cfg_rdata_r = 32'd0;
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 8'h40;
            timeout_cfg_reg <= {16'd1024, 16'd1024};
            clamp_min_reg <= 32'd0;
            clamp_max_reg <= 32'h7FFFFFFF;
            rate_limit_reg <= 32'd0;
            seq_seed_reg <= 32'd0;
            req_counter <= 32'd0;
            rsp_ok_counter <= 32'd0;
            rsp_rej_counter <= 32'd0;
            timeout_counter <= 32'd0;
            stale_counter <= 32'd0;
            fault_counter <= 32'd0;
            status_reg <= 8'd0;
            rsp_last_reg <= 32'd0;
            req_last_reg <= 32'd0;
            state <= ST_IDLE;
            seq_counter <= 16'd0;
            outstanding_seq <= 16'd0;
            outstanding_valid <= 1'b0;
            outstanding_launch <= 32'd0;
            cycle_count <= 32'd0;
            timeout_watchdog <= 32'd0;
            speed_sync <= 32'd0;
            final_cmd_reg <= 32'd0;
            last_cmd_reg <= 32'd0;
            req_pending <= 1'b0;
            req_valid_reg <= 1'b0;
            rsp_ready_reg <= 1'b0;
            actuator_valid_reg <= 1'b0;
            irq_reg <= 1'b0;
            req_data_reg <= 128'd0;
            rsp_data_q <= 128'd0;
        end else begin
            cycle_count <= cycle_count + 32'd1;
            speed_sync <= veh_speed_mps;
            req_pending <= req_pending;

            if (cfg_valid && cfg_write) begin
                case (cfg_addr)
                    ADDR_CTRL: begin
                        ctrl_reg[3:0] <= cfg_wdata[3:0];
                        if (cfg_wdata[4]) begin
                            status_reg <= 8'd0;
                            req_counter <= 32'd0;
                            rsp_ok_counter <= 32'd0;
                            rsp_rej_counter <= 32'd0;
                            timeout_counter <= 32'd0;
                            stale_counter <= 32'd0;
                            fault_counter <= 32'd0;
                        end
                    end
                    ADDR_TIMEOUT_CFG: timeout_cfg_reg <= cfg_wdata;
                    ADDR_CLAMP_MIN: clamp_min_reg <= cfg_wdata;
                    ADDR_CLAMP_MAX: clamp_max_reg <= cfg_wdata;
                    ADDR_RATE_LIMIT: rate_limit_reg <= cfg_wdata;
                    ADDR_SEQ_SEED: begin
                        seq_seed_reg <= cfg_wdata;
                        seq_counter <= cfg_wdata[15:0];
                    end
                    default: begin
                    end
                endcase
                if (cfg_addr == ADDR_CTRL) begin
                    ctrl_reg[7:4] <= cfg_wdata[7:4];
                end
            end

            if (clear_sticky) begin
                status_reg <= 8'd0;
                req_counter <= 32'd0;
                rsp_ok_counter <= 32'd0;
                rsp_rej_counter <= 32'd0;
                timeout_counter <= 32'd0;
                stale_counter <= 32'd0;
                fault_counter <= 32'd0;
            end

            if (!enable) begin
                outstanding_valid <= 1'b0;
                req_valid_reg <= 1'b0;
                rsp_ready_reg <= 1'b0;
                actuator_valid_reg <= 1'b1;
                final_cmd_reg <= clamp_min_reg;
                last_cmd_reg <= clamp_min_reg;
                state <= ST_FAILSAFE;
                status_reg[4] <= 1'b1;
            end else begin
                rsp_ready_reg <= 1'b1;
                if (req_issue_allowed && !req_valid_reg) begin
                    req_valid_reg <= 1'b1;
                    req_pending <= 1'b1;
                    outstanding_valid <= 1'b1;
                    outstanding_seq <= seq_counter;
                    outstanding_launch <= cycle_count;
                    timeout_watchdog <= 32'd0;
                    req_data_reg <= {req_data_word3, req_data_word2, req_data_word1, req_data_word0};
                    req_counter <= (req_counter == 32'hFFFFFFFF) ? req_counter : (req_counter + 32'd1);
                    req_last_reg <= {8'b0, req_flags, seq_counter};
                    seq_counter <= seq_counter + 16'd1;
                    state <= ST_WAIT_REQ;
                end
                if (req_launch_fire) begin
                    req_valid_reg <= 1'b0;
                    req_pending <= 1'b0;
                end

                if (outstanding_active) begin
                    timeout_watchdog <= timeout_watchdog + 32'd1;
                end else begin
                    timeout_watchdog <= 32'd0;
                end

                if (timeout_expired_now) begin
                    outstanding_valid <= 1'b0;
                    timeout_counter <= (timeout_counter == 32'hFFFFFFFF) ? timeout_counter : (timeout_counter + 32'd1);
                    status_reg[1] <= 1'b1;
                    status_reg[4] <= 1'b1;
                    state <= ST_FAILSAFE;
                end

                if (model_rsp_valid) begin
                    rsp_data_q <= model_rsp_data;
                    rsp_last_reg <= {8'd0, model_rsp_data[15:0], model_rsp_data[23:16]};
                    if (rsp_good) begin
                        rsp_ok_counter <= (rsp_ok_counter == 32'hFFFFFFFF) ? rsp_ok_counter : (rsp_ok_counter + 32'd1);
                        status_reg[7] <= 1'b1;
                        outstanding_valid <= 1'b0;
                        final_cmd_reg <= rate_limited_cmd;
                        last_cmd_reg <= rate_limited_cmd;
                        actuator_valid_reg <= 1'b1;
                        state <= ST_BUSY;
                    end else begin
                        rsp_rej_counter <= (rsp_rej_counter == 32'hFFFFFFFF) ? rsp_rej_counter : (rsp_rej_counter + 32'd1);
                        status_reg[6] <= 1'b1;
                        if (!rsp_fresh) begin
                            stale_counter <= (stale_counter == 32'hFFFFFFFF) ? stale_counter : (stale_counter + 32'd1);
                            status_reg[2] <= 1'b1;
                        end
                        outstanding_valid <= outstanding_active;
                        status_reg[3] <= 1'b1;
                    end
                end

                if (out_of_range_now) begin
                    status_reg[5] <= 1'b1;
                    if (!fallback_enable) begin
                        final_cmd_reg <= clamp_min_reg;
                        last_cmd_reg <= clamp_min_reg;
                        actuator_valid_reg <= 1'b1;
                        status_reg[4] <= 1'b1;
                    end
                end

                if (update_on_same || (rate_limited_cmd != last_cmd_reg)) begin
                    final_cmd_reg <= rate_limited_cmd;
                    last_cmd_reg <= rate_limited_cmd;
                    actuator_valid_reg <= 1'b1;
                end else begin
                    actuator_valid_reg <= actuator_valid_reg;
                end

                if (status_reg[1] || status_reg[3] || status_reg[4]) begin
                    fault_counter <= (fault_counter == 32'hFFFFFFFF) ? fault_counter : (fault_counter + 32'd1);
                end

                if (state == ST_FAILSAFE) begin
                    final_cmd_reg <= clamp_min_reg;
                    last_cmd_reg <= clamp_min_reg;
                    actuator_valid_reg <= 1'b1;
                end
            end

            if (irq_enable && (status_reg[1] || status_reg[3] || status_reg[4])) begin
                irq_reg <= 1'b1;
            end else if (!irq_enable) begin
                irq_reg <= 1'b0;
            end else begin
                irq_reg <= irq_reg;
            end
        end
    end
endmodule
