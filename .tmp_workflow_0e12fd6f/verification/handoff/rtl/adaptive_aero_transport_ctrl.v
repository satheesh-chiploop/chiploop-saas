module adaptive_aero_transport_ctrl (
    clk,
    rst_n,
    cfg_enable,
    cfg_soft_clear_faults,
    cfg_force_inhibit,
    cfg_queue_depth_enable,
    cfg_response_accept_enable,
    cfg_timeout_cycles,
    cfg_max_actuator_cmd,
    cfg_min_actuator_cmd,
    cfg_rate_limit_step,
    s_axis_req_data,
    s_axis_req_valid,
    s_axis_req_ready,
    m_axis_resp_data,
    m_axis_resp_valid,
    m_axis_resp_ready,
    m_axis_act_data,
    m_axis_act_valid,
    m_axis_act_ready,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    req_fifo_push_valid,
    req_fifo_push_data,
    req_fifo_push_ready,
    req_fifo_pop_valid,
    req_fifo_pop_data,
    req_fifo_pop_ready,
    req_record_seq,
    req_record_mode,
    req_record_geom_token,
    req_record_flow_speed,
    req_record_flow_alpha,
    req_record_flow_beta,
    req_record_valid,
    resp_record_seq,
    resp_record_status,
    resp_record_freshness,
    resp_record_complete,
    resp_record_ctrl_result,
    resp_record_valid,
    cmd_raw_data,
    cmd_raw_valid,
    cmd_clamped_data,
    cmd_clamped_valid,
    status_busy,
    status_response_valid_seen,
    status_stale_fault,
    status_timeout_fault,
    status_protocol_fault,
    status_fallback_active,
    status_request_pending,
    status_response_accepted,
    status_timeout_count,
    status_stale_reject_count,
    status_fallback_activation_count,
    status_last_seq_accepted,
    status_last_seq_rejected,
    active_seq,
    fsm_state
);
    input         clk;
    input         rst_n;
    input         cfg_enable;
    input         cfg_soft_clear_faults;
    input         cfg_force_inhibit;
    input         cfg_queue_depth_enable;
    input         cfg_response_accept_enable;
    input  [31:0] cfg_timeout_cycles;
    input  [15:0] cfg_max_actuator_cmd;
    input  [15:0] cfg_min_actuator_cmd;
    input  [15:0] cfg_rate_limit_step;
    input  [127:0] s_axis_req_data;
    input         s_axis_req_valid;
    output        s_axis_req_ready;
    output [127:0] m_axis_resp_data;
    output        m_axis_resp_valid;
    input         m_axis_resp_ready;
    output [63:0] m_axis_act_data;
    output        m_axis_act_valid;
    input         m_axis_act_ready;
    output        model_req_valid;
    output [127:0] model_req_data;
    input         model_req_ready;
    input         model_rsp_valid;
    input  [127:0] model_rsp_data;
    output        model_rsp_ready;
    output        req_fifo_push_valid;
    output [127:0] req_fifo_push_data;
    input         req_fifo_push_ready;
    output        req_fifo_pop_valid;
    input  [127:0] req_fifo_pop_data;
    input         req_fifo_pop_ready;
    output [31:0] req_record_seq;
    output [3:0] req_record_mode;
    output [15:0] req_record_geom_token;
    output [15:0] req_record_flow_speed;
    output [11:0] req_record_flow_alpha;
    output [11:0] req_record_flow_beta;
    output        req_record_valid;
    input  [31:0] resp_record_seq;
    input  [3:0] resp_record_status;
    input  [3:0] resp_record_freshness;
    input         resp_record_complete;
    input  [15:0] resp_record_ctrl_result;
    input         resp_record_valid;
    input  [63:0] cmd_raw_data;
    input         cmd_raw_valid;
    output [63:0] cmd_clamped_data;
    output        cmd_clamped_valid;
    output        status_busy;
    output        status_response_valid_seen;
    output        status_stale_fault;
    output        status_timeout_fault;
    output        status_protocol_fault;
    output        status_fallback_active;
    output        status_request_pending;
    output        status_response_accepted;
    output [31:0] status_timeout_count;
    output [31:0] status_stale_reject_count;
    output [31:0] status_fallback_activation_count;
    output [31:0] status_last_seq_accepted;
    output [31:0] status_last_seq_rejected;
    output [31:0] active_seq;
    output [2:0] fsm_state;
    localparam [2:0] ST_IDLE = 3'd0;
    localparam [2:0] ST_ISSUE_REQ = 3'd1;
    localparam [2:0] ST_WAIT_RESP = 3'd2;
    localparam [2:0] ST_VALIDATE_RESP = 3'd3;
    localparam [2:0] ST_APPLY_CMD = 3'd4;
    localparam [2:0] ST_FAULT = 3'd5;

    reg [2:0] state_r, state_n;
    reg [31:0] seq_r;
    reg [31:0] watchdog_r;
    reg [31:0] active_seq_r;
    reg [31:0] last_seq_accepted_r;
    reg [31:0] last_seq_rejected_r;
    reg [31:0] timeout_count_r;
    reg [31:0] stale_reject_count_r;
    reg [31:0] fallback_activation_count_r;
    reg status_response_valid_seen_r;
    reg status_stale_fault_r;
    reg status_timeout_fault_r;
    reg status_protocol_fault_r;
    reg status_fallback_active_r;
    reg status_request_pending_r;
    reg status_response_accepted_r;
    reg [63:0] cmd_clamped_data_r;
    reg cmd_clamped_valid_r;
    reg [127:0] m_axis_resp_data_r;
    reg m_axis_resp_valid_r;
    reg [63:0] m_axis_act_data_r;
    reg m_axis_act_valid_r;
    reg model_req_valid_r;
    reg [127:0] model_req_data_r;
    reg model_rsp_ready_r;
    reg req_fifo_push_valid_r;
    reg [127:0] req_fifo_push_data_r;
    reg req_fifo_pop_valid_r;
    reg [31:0] req_record_seq_r;
    reg [3:0] req_record_mode_r;
    reg [15:0] req_record_geom_token_r;
    reg [15:0] req_record_flow_speed_r;
    reg [11:0] req_record_flow_alpha_r;
    reg [11:0] req_record_flow_beta_r;
    reg req_record_valid_r;
    reg s_axis_req_ready_r;
    reg status_busy_r;

    wire [31:0] parsed_seq;
    wire [3:0] parsed_mode;
    wire [15:0] parsed_geom_token;
    wire [15:0] parsed_flow_speed;
    wire [11:0] parsed_flow_alpha;
    wire [11:0] parsed_flow_beta;
    wire [15:0] raw_cmd_lo;
    wire [15:0] raw_cmd_hi;
    wire [15:0] raw_cmd_val;
    wire [15:0] clamped_min;
    wire [15:0] clamped_max;
    wire [15:0] clamped_step;
    wire [15:0] clamped_prev;
    wire [15:0] clamped_next;
    wire [15:0] resp_cmd;
    wire valid_resp;
    wire timeout_expired;
    wire fault_any;
    wire can_accept_req;
    wire request_event;
    wire response_event;

    assign parsed_seq = s_axis_req_data[31:0];
    assign parsed_mode = s_axis_req_data[35:32];
    assign parsed_geom_token = s_axis_req_data[51:36];
    assign parsed_flow_speed = s_axis_req_data[67:52];
    assign parsed_flow_alpha = s_axis_req_data[79:68];
    assign parsed_flow_beta = s_axis_req_data[91:80];

    assign raw_cmd_lo = cmd_raw_data[15:0];
    assign raw_cmd_hi = cmd_raw_data[31:16];
    assign raw_cmd_val = cmd_raw_data[47:32];
    assign resp_cmd = resp_record_ctrl_result;

    assign clamped_min = cfg_min_actuator_cmd;
    assign clamped_max = cfg_max_actuator_cmd;
    assign clamped_step = cfg_rate_limit_step;
    assign clamped_prev = m_axis_act_data_r[15:0];
    assign valid_resp = resp_record_valid && cfg_response_accept_enable && (resp_record_seq == active_seq_r) && resp_record_complete && (resp_record_freshness != 4'd0) && !status_timeout_fault_r && !status_protocol_fault_r && !status_stale_fault_r;
    assign timeout_expired = (cfg_timeout_cycles != 32'd0) && (watchdog_r >= cfg_timeout_cycles);
    assign fault_any = status_stale_fault_r | status_timeout_fault_r | status_protocol_fault_r;
    assign can_accept_req = cfg_enable && !cfg_force_inhibit && !fault_any;
    assign request_event = s_axis_req_valid && s_axis_req_ready_r;
    assign response_event = model_rsp_valid && model_rsp_ready_r;

    assign s_axis_req_ready = s_axis_req_ready_r;
    assign m_axis_resp_data = m_axis_resp_data_r;
    assign m_axis_resp_valid = m_axis_resp_valid_r;
    assign m_axis_act_data = m_axis_act_data_r;
    assign m_axis_act_valid = m_axis_act_valid_r;
    assign model_req_valid = model_req_valid_r;
    assign model_req_data = model_req_data_r;
    assign model_rsp_ready = model_rsp_ready_r;
    assign req_fifo_push_valid = req_fifo_push_valid_r;
    assign req_fifo_push_data = req_fifo_push_data_r;
    assign req_fifo_pop_valid = req_fifo_pop_valid_r;
    assign req_record_seq = req_record_seq_r;
    assign req_record_mode = req_record_mode_r;
    assign req_record_geom_token = req_record_geom_token_r;
    assign req_record_flow_speed = req_record_flow_speed_r;
    assign req_record_flow_alpha = req_record_flow_alpha_r;
    assign req_record_flow_beta = req_record_flow_beta_r;
    assign req_record_valid = req_record_valid_r;
    assign cmd_clamped_data = cmd_clamped_data_r;
    assign cmd_clamped_valid = cmd_clamped_valid_r;
    assign status_busy = status_busy_r;
    assign status_response_valid_seen = status_response_valid_seen_r;
    assign status_stale_fault = status_stale_fault_r;
    assign status_timeout_fault = status_timeout_fault_r;
    assign status_protocol_fault = status_protocol_fault_r;
    assign status_fallback_active = status_fallback_active_r;
    assign status_request_pending = status_request_pending_r;
    assign status_response_accepted = status_response_accepted_r;
    assign status_timeout_count = timeout_count_r;
    assign status_stale_reject_count = stale_reject_count_r;
    assign status_fallback_activation_count = fallback_activation_count_r;
    assign status_last_seq_accepted = last_seq_accepted_r;
    assign status_last_seq_rejected = last_seq_rejected_r;
    assign active_seq = active_seq_r;
    assign fsm_state = state_r;

    always @(*) begin
        state_n = state_r;
        s_axis_req_ready_r = 1'b0;
        m_axis_resp_data_r = model_rsp_data;
        m_axis_resp_valid_r = 1'b0;
        m_axis_act_data_r = 64'd0;
        m_axis_act_valid_r = 1'b0;
        model_req_valid_r = 1'b0;
        model_req_data_r = 128'd0;
        model_rsp_ready_r = 1'b0;
        req_fifo_push_valid_r = 1'b0;
        req_fifo_push_data_r = 128'd0;
        req_fifo_pop_valid_r = 1'b0;
        req_record_seq_r = parsed_seq;
        req_record_mode_r = parsed_mode;
        req_record_geom_token_r = parsed_geom_token;
        req_record_flow_speed_r = parsed_flow_speed;
        req_record_flow_alpha_r = parsed_flow_alpha;
        req_record_flow_beta_r = parsed_flow_beta;
        req_record_valid_r = 1'b0;
        cmd_clamped_data_r = cmd_raw_data;
        cmd_clamped_valid_r = 1'b0;
        status_busy_r = (state_r != ST_IDLE);
        status_request_pending_r = (state_r == ST_WAIT_RESP) || (state_r == ST_VALIDATE_RESP) || (state_r == ST_ISSUE_REQ);
        status_response_accepted_r = 1'b0;

        if (!cfg_enable || cfg_force_inhibit || fault_any) begin
            state_n = ST_FAULT;
        end else begin
            case (state_r)
                ST_IDLE: begin
                    s_axis_req_ready_r = 1'b1;
                    if (request_event) begin
                        state_n = ST_ISSUE_REQ;
                    end
                end
                ST_ISSUE_REQ: begin
                    model_req_valid_r = 1'b1;
                    model_req_data_r = s_axis_req_data;
                    req_fifo_push_valid_r = 1'b1;
                    req_fifo_push_data_r = s_axis_req_data;
                    req_record_valid_r = 1'b1;
                    if (model_req_ready && req_fifo_push_ready) begin
                        state_n = ST_WAIT_RESP;
                    end
                end
                ST_WAIT_RESP: begin
                    model_rsp_ready_r = 1'b1;
                    if (response_event) begin
                        state_n = ST_VALIDATE_RESP;
                    end else if (timeout_expired) begin
                        state_n = ST_FAULT;
                    end
                end
                ST_VALIDATE_RESP: begin
                    model_rsp_ready_r = 1'b1;
                    m_axis_resp_data_r = model_rsp_data;
                    m_axis_resp_valid_r = model_rsp_valid;
                    if (valid_resp) begin
                        state_n = ST_APPLY_CMD;
                    end else begin
                        state_n = ST_FAULT;
                    end
                end
                ST_APPLY_CMD: begin
                    cmd_clamped_valid_r = cmd_raw_valid && !cfg_force_inhibit && cfg_enable;
                    if (cmd_raw_valid) begin
                        if (cmd_raw_data[15:0] > clamped_max) begin
                            cmd_clamped_data_r = {48'd0, clamped_max};
                        end else if (cmd_raw_data[15:0] < clamped_min) begin
                            cmd_clamped_data_r = {48'd0, clamped_min};
                        end else begin
                            if (clamped_step != 16'd0 && (cmd_raw_data[15:0] > clamped_prev + clamped_step)) begin
                                cmd_clamped_data_r = {48'd0, (clamped_prev + clamped_step)};
                            end else if (clamped_step != 16'd0 && (cmd_raw_data[15:0] + clamped_step < clamped_prev)) begin
                                cmd_clamped_data_r = {48'd0, (clamped_prev - clamped_step)};
                            end else begin
                                cmd_clamped_data_r = cmd_raw_data;
                            end
                        end
                    end
                    if (cmd_clamped_valid_r && m_axis_act_ready) begin
                        state_n = ST_IDLE;
                        status_response_accepted_r = 1'b1;
                    end
                end
                ST_FAULT: begin
                    if (cfg_soft_clear_faults && cfg_enable && !cfg_force_inhibit) begin
                        state_n = ST_IDLE;
                    end
                end
                default: begin
                    state_n = ST_FAULT;
                end
            endcase
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_r <= ST_IDLE;
            seq_r <= 32'd0;
            watchdog_r <= 32'd0;
            active_seq_r <= 32'd0;
            last_seq_accepted_r <= 32'd0;
            last_seq_rejected_r <= 32'd0;
            timeout_count_r <= 32'd0;
            stale_reject_count_r <= 32'd0;
            fallback_activation_count_r <= 32'd0;
            status_response_valid_seen_r <= 1'b0;
            status_stale_fault_r <= 1'b0;
            status_timeout_fault_r <= 1'b0;
            status_protocol_fault_r <= 1'b0;
            status_fallback_active_r <= 1'b1;
        end else begin
            state_r <= state_n;
            if (cfg_soft_clear_faults) begin
                status_stale_fault_r <= 1'b0;
                status_timeout_fault_r <= 1'b0;
                status_protocol_fault_r <= 1'b0;
            end
            if (request_event) begin
                seq_r <= seq_r + 32'd1;
                active_seq_r <= seq_r + 32'd1;
                watchdog_r <= 32'd0;
                status_fallback_active_r <= 1'b0;
            end else if (state_r == ST_WAIT_RESP) begin
                watchdog_r <= watchdog_r + 32'd1;
            end
            if (timeout_expired) begin
                status_timeout_fault_r <= 1'b1;
                timeout_count_r <= timeout_count_r + 32'd1;
                last_seq_rejected_r <= active_seq_r;
                status_fallback_active_r <= 1'b1;
                fallback_activation_count_r <= fallback_activation_count_r + 32'd1;
            end
            if (response_event) begin
                status_response_valid_seen_r <= 1'b1;
                if (valid_resp) begin
                    last_seq_accepted_r <= resp_record_seq;
                    status_fallback_active_r <= 1'b0;
                end else begin
                    status_stale_fault_r <= 1'b1;
                    stale_reject_count_r <= stale_reject_count_r + 32'd1;
                    last_seq_rejected_r <= resp_record_seq;
                    status_fallback_active_r <= 1'b1;
                    fallback_activation_count_r <= fallback_activation_count_r + 32'd1;
                end
            end
            if (state_n == ST_FAULT && state_r != ST_FAULT) begin
                status_protocol_fault_r <= 1'b1;
                status_fallback_active_r <= 1'b1;
                fallback_activation_count_r <= fallback_activation_count_r + 32'd1;
            end
            if (state_r == ST_APPLY_CMD && cmd_clamped_valid_r && m_axis_act_ready) begin
                status_fallback_active_r <= 1'b0;
            end
        end
    end
endmodule
