module adaptive_aero_control_top (
    clk,
    rst_n,
    csr_addr,
    csr_wdata,
    csr_valid,
    csr_we,
    csr_rdata,
    csr_ready,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    actuator_cmd_out,
    actuator_cmd_valid,
    actuator_cmd_surrogate_valid,
    fault_status_out,
    status_out
);

input clk;
input rst_n;
input [5:0] csr_addr;
input [63:0] csr_wdata;
input csr_valid;
input csr_we;
output [63:0] csr_rdata;
output csr_ready;
output model_req_valid;
output [127:0] model_req_data;
input model_req_ready;
input model_rsp_valid;
input [127:0] model_rsp_data;
output model_rsp_ready;
output [31:0] actuator_cmd_out;
output actuator_cmd_valid;
output actuator_cmd_surrogate_valid;
output [15:0] fault_status_out;
output [15:0] status_out;
reg [63:0] csr_rdata_r;
reg csr_ready_r;
reg model_req_valid_r;
reg [127:0] model_req_data_r;
reg model_rsp_ready_r;
reg [31:0] actuator_cmd_out_r;
reg actuator_cmd_valid_r;
reg actuator_cmd_surrogate_valid_r;
reg [15:0] fault_status_out_r;
reg [15:0] status_out_r;
assign csr_rdata = csr_rdata_r;
assign csr_ready = csr_ready_r;
assign model_req_valid = model_req_valid_r;
assign model_req_data = model_req_data_r;
assign model_rsp_ready = model_rsp_ready_r;
assign actuator_cmd_out = actuator_cmd_out_r;
assign actuator_cmd_valid = actuator_cmd_valid_r;
assign actuator_cmd_surrogate_valid = actuator_cmd_surrogate_valid_r;
assign fault_status_out = fault_status_out_r;
assign status_out = status_out_r;

localparam [2:0] ST_IDLE       = 3'd0;
localparam [2:0] ST_ISSUE_REQ   = 3'd1;
localparam [2:0] ST_WAIT_RSP    = 3'd2;
localparam [2:0] ST_VALIDATE_RSP= 3'd3;
localparam [2:0] ST_APPLY_CMD   = 3'd4;
localparam [2:0] ST_FALLBACK    = 3'd5;
localparam [2:0] ST_FAULT_HOLD  = 3'd6;

localparam [5:0] REG_CTRL         = 6'd0;
localparam [5:0] REG_TIMING_CFG   = 6'd1;
localparam [5:0] REG_CLAMP_CFG    = 6'd2;
localparam [5:0] REG_FALLBACK_CFG = 6'd3;
localparam [5:0] REG_REQ_CAPTURE  = 6'd4;
localparam [5:0] REG_SEQ_STATUS   = 6'd5;
localparam [5:0] REG_ACTUATOR_OUT = 6'd6;
localparam [5:0] REG_FAULT_STATUS = 6'd7;

localparam [5:0] ERR_NONE      = 6'd0;
localparam [5:0] ERR_STALE     = 6'd1;
localparam [5:0] ERR_TIMEOUT   = 6'd2;
localparam [5:0] ERR_BAD_RSP   = 6'd3;
localparam [5:0] ERR_MISMATCH  = 6'd4;
localparam [5:0] ERR_INACTIVE  = 6'd5;
localparam [5:0] ERR_VELOCITY  = 6'd6;

reg [2:0] state_r, state_n;
reg [2:0] operating_mode_r;
reg request_arm_r;
reg watchdog_enable_r;
reg host_inactivity_enable_r;
reg [15:0] timeout_threshold_r;
reg [15:0] stale_age_threshold_r;
reg [15:0] inactivity_threshold_r;
reg [31:0] actuator_min_r;
reg [31:0] actuator_max_r;
reg [31:0] fallback_cmd_r;
reg fallback_valid_r;
reg [15:0] req_transaction_id_r;
reg [15:0] req_geometry_handle_r;
reg [15:0] req_stream_velocity_r;
reg [15:0] req_flow_summary_r;
reg [15:0] accepted_seq_r;
reg [15:0] seq_age_r;
reg [15:0] watchdog_cnt_r;
reg [15:0] inactivity_cnt_r;
reg [15:0] last_rsp_transaction_id_r;
reg [31:0] last_rsp_cmd_r;
reg last_rsp_status_ok_r;
reg busy_r;
reg response_valid_r;
reg stale_reject_r;
reg timeout_fault_r;
reg invalid_response_fault_r;
reg response_mismatch_fault_r;
reg host_inactivity_fault_r;
reg clamp_active_r;
reg fallback_active_r;
reg [5:0] last_error_code_r;
reg latched_fault_r;
reg ack_response_r;
reg clear_faults_r;

reg [63:0] csr_read_mux;
reg csr_write_hit;
reg [127:0] model_req_data_next;
reg model_req_accept;
reg model_rsp_accept;
reg [31:0] candidate_cmd;
reg [31:0] clamped_cmd;
reg [31:0] fallback_cmd_eff;
reg clamp_needed;
reg velocity_ok;
reg stale_ok;
reg timeout_hit;
reg inactivity_hit;
reg rsp_id_match;
reg rsp_complete;
reg rsp_status_ok;
reg rsp_fresh;

always @(*) begin
    csr_read_mux = 64'h0000000000000000;
    csr_write_hit = 1'b0;
    model_req_accept = 1'b0;
    model_rsp_accept = 1'b0;
    candidate_cmd = last_rsp_cmd_r;
    clamped_cmd = last_rsp_cmd_r;
    fallback_cmd_eff = fallback_cmd_r;
    clamp_needed = 1'b0;
    velocity_ok = 1'b1;
    stale_ok = 1'b1;
    timeout_hit = 1'b0;
    inactivity_hit = 1'b0;
    rsp_id_match = 1'b0;
    rsp_complete = 1'b0;
    rsp_status_ok = 1'b0;
    rsp_fresh = 1'b0;
    model_req_data_next = 128'h00000000000000000000000000000000;
    state_n = state_r;

    if (fallback_cmd_eff < actuator_min_r)
        fallback_cmd_eff = actuator_min_r;
    else if (fallback_cmd_eff > actuator_max_r)
        fallback_cmd_eff = actuator_max_r;

    velocity_ok = (req_stream_velocity_r >= 16'd20) && (req_stream_velocity_r <= 16'd55);
    stale_ok = (seq_age_r <= stale_age_threshold_r);
    timeout_hit = watchdog_enable_r && (watchdog_cnt_r >= timeout_threshold_r) && (state_r == ST_WAIT_RSP || state_r == ST_VALIDATE_RSP);
    inactivity_hit = host_inactivity_enable_r && (inactivity_threshold_r != 16'd0) && (inactivity_cnt_r >= inactivity_threshold_r);
    rsp_id_match = (model_rsp_data[15:0] == req_transaction_id_r);
    rsp_complete = model_rsp_data[33];
    rsp_status_ok = model_rsp_data[34];
    rsp_fresh = (model_rsp_data[63:48] == accepted_seq_r);

    case (state_r)
        ST_IDLE: begin
            if (request_arm_r && !latched_fault_r) begin
                if (!velocity_ok || !stale_ok) begin
                    state_n = ST_FALLBACK;
                end else begin
                    state_n = ST_ISSUE_REQ;
                end
            end
        end
        ST_ISSUE_REQ: begin
            model_req_data_next[15:0] = req_transaction_id_r;
            model_req_data_next[31:16] = req_geometry_handle_r;
            model_req_data_next[47:32] = req_stream_velocity_r;
            model_req_data_next[63:48] = req_flow_summary_r;
            model_req_data_next[64] = operating_mode_r[0];
            model_req_data_next[65] = operating_mode_r[1];
            model_req_data_next[66] = operating_mode_r[2];
            model_req_data_next[67] = watchdog_enable_r;
            model_req_data_next[68] = host_inactivity_enable_r;
            model_req_data_next[69] = fallback_valid_r;
            model_req_data_next[127:70] = 58'd0;
            if (model_req_ready)
                state_n = ST_WAIT_RSP;
        end
        ST_WAIT_RSP: begin
            model_req_data_next[15:0] = req_transaction_id_r;
            model_req_data_next[31:16] = req_geometry_handle_r;
            model_req_data_next[47:32] = req_stream_velocity_r;
            model_req_data_next[63:48] = req_flow_summary_r;
            model_req_data_next[64] = operating_mode_r[0];
            model_req_data_next[65] = operating_mode_r[1];
            model_req_data_next[66] = operating_mode_r[2];
            model_req_data_next[67] = watchdog_enable_r;
            model_req_data_next[68] = host_inactivity_enable_r;
            model_req_data_next[69] = fallback_valid_r;
            model_req_data_next[127:70] = 58'd0;
            if (timeout_hit) begin
                state_n = ST_FALLBACK;
            end else if (model_rsp_valid) begin
                state_n = ST_VALIDATE_RSP;
            end
        end
        ST_VALIDATE_RSP: begin
            if (timeout_hit) begin
                state_n = ST_FALLBACK;
            end else if (!rsp_id_match || !rsp_complete || !rsp_status_ok || !rsp_fresh) begin
                state_n = ST_FAULT_HOLD;
            end else begin
                state_n = ST_APPLY_CMD;
            end
        end
        ST_APPLY_CMD: begin
            state_n = ST_IDLE;
        end
        ST_FALLBACK: begin
            state_n = ST_FAULT_HOLD;
        end
        ST_FAULT_HOLD: begin
            if (clear_faults_r && !latched_fault_r)
                state_n = ST_IDLE;
        end
        default: begin
            state_n = ST_IDLE;
        end
    endcase

    if (state_r == ST_IDLE) begin
        busy_r = 1'b0;
    end else begin
        busy_r = 1'b1;
    end

    case (csr_addr)
        REG_CTRL: csr_read_mux = {2'b0, 56'd0, host_inactivity_enable_r, watchdog_enable_r, request_arm_r, operating_mode_r};
        REG_TIMING_CFG: csr_read_mux = {16'd0, inactivity_threshold_r, stale_age_threshold_r, timeout_threshold_r};
        REG_CLAMP_CFG: csr_read_mux = {actuator_max_r, actuator_min_r};
        REG_FALLBACK_CFG: csr_read_mux = {31'd0, fallback_valid_r, fallback_cmd_r};
        REG_REQ_CAPTURE: csr_read_mux = {req_flow_summary_r, req_stream_velocity_r, req_geometry_handle_r, req_transaction_id_r};
        REG_SEQ_STATUS: csr_read_mux = {48'd0, last_error_code_r, fallback_active_r, clamp_active_r, invalid_response_fault_r, timeout_fault_r, stale_reject_r, response_valid_r, busy_r, state_r};
        REG_ACTUATOR_OUT: csr_read_mux = {30'd0, actuator_cmd_valid_r, actuator_cmd_surrogate_valid_r, actuator_cmd_out_r};
        REG_FAULT_STATUS: csr_read_mux = {50'd0, last_error_code_r, fallback_active_r, clamp_active_r, host_inactivity_fault_r, response_mismatch_fault_r, stale_reject_r, invalid_response_fault_r, timeout_fault_r, latched_fault_r};
        default: csr_read_mux = 64'h0000000000000000;
    endcase

    if (csr_valid && !csr_we) begin
    end

    if (csr_valid && csr_we) begin
        csr_write_hit = 1'b1;
    end

    if (state_r == ST_ISSUE_REQ || state_r == ST_WAIT_RSP) begin
    end

    if (state_r == ST_WAIT_RSP || state_r == ST_VALIDATE_RSP) begin
    end

    if (state_r == ST_APPLY_CMD) begin
        candidate_cmd = last_rsp_cmd_r;
        if (candidate_cmd < actuator_min_r)
            clamped_cmd = actuator_min_r;
        else if (candidate_cmd > actuator_max_r)
            clamped_cmd = actuator_max_r;
        else
            clamped_cmd = candidate_cmd;
        clamp_needed = (clamped_cmd != candidate_cmd);
    end else begin
        clamped_cmd = last_rsp_cmd_r;
        clamp_needed = 1'b0;
    end

    if (state_r == ST_FALLBACK) begin
        if (fallback_valid_r)
            clamped_cmd = fallback_cmd_eff;
        else
            clamped_cmd = actuator_min_r;
        clamp_needed = (clamped_cmd != fallback_cmd_eff);
    end

    if (timeout_hit)
        timeout_hit = 1'b1;

    if (!velocity_ok || !stale_ok)
        stale_ok = stale_ok;

    if (host_inactivity_enable_r && inactivity_hit)
        inactivity_hit = 1'b1;
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state_r <= ST_IDLE;
        operating_mode_r <= 3'd0;
        request_arm_r <= 1'b0;
        watchdog_enable_r <= 1'b1;
        host_inactivity_enable_r <= 1'b0;
        timeout_threshold_r <= 16'd1000;
        stale_age_threshold_r <= 16'd32;
        inactivity_threshold_r <= 16'd0;
        actuator_min_r <= 32'd0;
        actuator_max_r <= 32'hFFFFFFFF;
        fallback_cmd_r <= 32'd0;
        fallback_valid_r <= 1'b1;
        req_transaction_id_r <= 16'd0;
        req_geometry_handle_r <= 16'd0;
        req_stream_velocity_r <= 16'd20;
        req_flow_summary_r <= 16'd0;
        accepted_seq_r <= 16'd0;
        seq_age_r <= 16'd0;
        watchdog_cnt_r <= 16'd0;
        inactivity_cnt_r <= 16'd0;
        last_rsp_transaction_id_r <= 16'd0;
        last_rsp_cmd_r <= 32'd0;
        last_rsp_status_ok_r <= 1'b0;
        response_valid_r <= 1'b0;
        stale_reject_r <= 1'b0;
        timeout_fault_r <= 1'b0;
        invalid_response_fault_r <= 1'b0;
        response_mismatch_fault_r <= 1'b0;
        host_inactivity_fault_r <= 1'b0;
        clamp_active_r <= 1'b0;
        fallback_active_r <= 1'b0;
        last_error_code_r <= ERR_NONE;
        latched_fault_r <= 1'b0;
        ack_response_r <= 1'b0;
        clear_faults_r <= 1'b0;
        csr_rdata_r <= 64'd0;
        csr_ready_r <= 1'b1;
        model_req_valid_r <= 1'b0;
        model_req_data_r <= 128'd0;
        model_rsp_ready_r <= 1'b0;
        actuator_cmd_out_r <= 32'd0;
        actuator_cmd_valid_r <= 1'b0;
        actuator_cmd_surrogate_valid_r <= 1'b0;
        fault_status_out_r <= 16'd0;
        status_out_r <= 16'd0;
    end else begin
        clear_faults_r <= 1'b0;
        ack_response_r <= 1'b0;

        if (csr_valid && csr_we) begin
            case (csr_addr)
                REG_CTRL: begin
                    operating_mode_r <= csr_wdata[2:0];
                    request_arm_r <= csr_wdata[3];
                    watchdog_enable_r <= csr_wdata[4];
                    host_inactivity_enable_r <= csr_wdata[5];
                    clear_faults_r <= csr_wdata[6];
                    ack_response_r <= csr_wdata[7];
                end
                REG_TIMING_CFG: begin
                    timeout_threshold_r <= csr_wdata[15:0];
                    stale_age_threshold_r <= csr_wdata[31:16];
                    inactivity_threshold_r <= csr_wdata[47:32];
                end
                REG_CLAMP_CFG: begin
                    actuator_min_r <= csr_wdata[31:0];
                    actuator_max_r <= csr_wdata[63:32];
                end
                REG_FALLBACK_CFG: begin
                    fallback_cmd_r <= csr_wdata[31:0];
                    fallback_valid_r <= csr_wdata[32];
                end
                REG_REQ_CAPTURE: begin
                    req_transaction_id_r <= csr_wdata[15:0];
                    req_geometry_handle_r <= csr_wdata[31:16];
                    req_stream_velocity_r <= csr_wdata[47:32];
                    req_flow_summary_r <= csr_wdata[63:48];
                    seq_age_r <= 16'd0;
                    inactivity_cnt_r <= 16'd0;
                end
                default: begin
                end
            endcase
        end

        if (state_r == ST_IDLE) begin
            model_req_valid_r <= 1'b0;
            model_rsp_ready_r <= 1'b0;
            actuator_cmd_valid_r <= 1'b0;
            actuator_cmd_surrogate_valid_r <= 1'b0;
            if (request_arm_r && !latched_fault_r) begin
                if ((req_stream_velocity_r < 16'd20) || (req_stream_velocity_r > 16'd55) || (seq_age_r > stale_age_threshold_r)) begin
                    stale_reject_r <= 1'b1;
                    latched_fault_r <= 1'b1;
                    last_error_code_r <= ((req_stream_velocity_r < 16'd20) || (req_stream_velocity_r > 16'd55)) ? ERR_VELOCITY : ERR_STALE;
                    state_r <= ST_FALLBACK;
                end else begin
                    state_r <= ST_ISSUE_REQ;
                    watchdog_cnt_r <= 16'd0;
                    inactivity_cnt_r <= 16'd0;
                    accepted_seq_r <= accepted_seq_r + 16'd1;
                    stale_reject_r <= 1'b0;
                    response_valid_r <= 1'b0;
                end
            end
        end else if (state_r == ST_ISSUE_REQ) begin
            model_req_valid_r <= 1'b1;
            model_req_data_r <= model_req_data_next;
            if (model_req_ready) begin
                state_r <= ST_WAIT_RSP;
                watchdog_cnt_r <= 16'd0;
                inactivity_cnt_r <= 16'd0;
            end
        end else if (state_r == ST_WAIT_RSP) begin
            model_req_valid_r <= 1'b1;
            model_req_data_r <= model_req_data_next;
            model_rsp_ready_r <= 1'b1;
            if (watchdog_enable_r && watchdog_cnt_r < 16'hFFFF)
                watchdog_cnt_r <= watchdog_cnt_r + 16'd1;
            if (host_inactivity_enable_r && inactivity_cnt_r < 16'hFFFF)
                inactivity_cnt_r <= inactivity_cnt_r + 16'd1;
            seq_age_r <= seq_age_r + 16'd1;
            if (watchdog_enable_r && (watchdog_cnt_r >= timeout_threshold_r)) begin
                timeout_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_TIMEOUT;
                state_r <= ST_FALLBACK;
            end else if (model_rsp_valid) begin
                state_r <= ST_VALIDATE_RSP;
            end
        end else if (state_r == ST_VALIDATE_RSP) begin
            model_rsp_ready_r <= 1'b1;
            if (watchdog_enable_r && (watchdog_cnt_r >= timeout_threshold_r)) begin
                timeout_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_TIMEOUT;
                state_r <= ST_FALLBACK;
            end else if (model_rsp_data[15:0] != req_transaction_id_r) begin
                response_mismatch_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_MISMATCH;
                state_r <= ST_FAULT_HOLD;
            end else if (!model_rsp_data[33] || !model_rsp_data[34]) begin
                invalid_response_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_BAD_RSP;
                state_r <= ST_FAULT_HOLD;
            end else if (model_rsp_data[63:48] != accepted_seq_r) begin
                response_mismatch_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_MISMATCH;
                state_r <= ST_FAULT_HOLD;
            end else begin
                last_rsp_transaction_id_r <= model_rsp_data[15:0];
                last_rsp_cmd_r <= model_rsp_data[31:0];
                last_rsp_status_ok_r <= 1'b1;
                response_valid_r <= 1'b1;
                state_r <= ST_APPLY_CMD;
            end
        end else if (state_r == ST_APPLY_CMD) begin
            if (last_rsp_cmd_r < actuator_min_r) begin
                actuator_cmd_out_r <= actuator_min_r;
                clamp_active_r <= 1'b1;
            end else if (last_rsp_cmd_r > actuator_max_r) begin
                actuator_cmd_out_r <= actuator_max_r;
                clamp_active_r <= 1'b1;
            end else begin
                actuator_cmd_out_r <= last_rsp_cmd_r;
                clamp_active_r <= 1'b0;
            end
            actuator_cmd_valid_r <= 1'b1;
            actuator_cmd_surrogate_valid_r <= 1'b1;
            fallback_active_r <= 1'b0;
            state_r <= ST_IDLE;
        end else if (state_r == ST_FALLBACK) begin
            if (fallback_valid_r) begin
                if (fallback_cmd_r < actuator_min_r) begin
                    actuator_cmd_out_r <= actuator_min_r;
                    clamp_active_r <= 1'b1;
                end else if (fallback_cmd_r > actuator_max_r) begin
                    actuator_cmd_out_r <= actuator_max_r;
                    clamp_active_r <= 1'b1;
                end else begin
                    actuator_cmd_out_r <= fallback_cmd_r;
                    clamp_active_r <= 1'b0;
                end
            end else begin
                actuator_cmd_out_r <= actuator_min_r;
                clamp_active_r <= 1'b1;
            end
            actuator_cmd_valid_r <= 1'b1;
            actuator_cmd_surrogate_valid_r <= 1'b0;
            fallback_active_r <= 1'b1;
            latched_fault_r <= 1'b1;
            if (last_error_code_r == ERR_NONE)
                last_error_code_r <= ERR_BAD_RSP;
            state_r <= ST_FAULT_HOLD;
        end else begin
            if (clear_faults_r) begin
                stale_reject_r <= 1'b0;
                timeout_fault_r <= 1'b0;
                invalid_response_fault_r <= 1'b0;
                response_mismatch_fault_r <= 1'b0;
                host_inactivity_fault_r <= 1'b0;
                latched_fault_r <= 1'b0;
                last_error_code_r <= ERR_NONE;
                response_valid_r <= 1'b0;
                clamp_active_r <= 1'b0;
                fallback_active_r <= 1'b0;
                state_r <= ST_IDLE;
            end
        end

        if (ack_response_r) begin
            response_valid_r <= 1'b0;
            actuator_cmd_valid_r <= 1'b0;
        end

        if (host_inactivity_enable_r && inactivity_threshold_r != 16'd0) begin
            if (inactivity_cnt_r >= inactivity_threshold_r) begin
                host_inactivity_fault_r <= 1'b1;
                latched_fault_r <= 1'b1;
                last_error_code_r <= ERR_INACTIVE;
            end
        end

        csr_rdata_r <= csr_read_mux;
        csr_ready_r <= 1'b1;
        fault_status_out_r[0] <= latched_fault_r;
        fault_status_out_r[1] <= timeout_fault_r;
        fault_status_out_r[2] <= invalid_response_fault_r;
        fault_status_out_r[3] <= stale_reject_r;
        fault_status_out_r[4] <= response_mismatch_fault_r;
        fault_status_out_r[5] <= host_inactivity_fault_r;
        fault_status_out_r[6] <= clamp_active_r;
        fault_status_out_r[7] <= fallback_active_r;
        fault_status_out_r[13:8] <= last_error_code_r;
        fault_status_out_r[15:14] <= 2'b00;
        status_out_r[2:0] <= state_r;
        status_out_r[3] <= busy_r;
        status_out_r[4] <= response_valid_r;
        status_out_r[5] <= stale_reject_r;
        status_out_r[6] <= timeout_fault_r;
        status_out_r[7] <= invalid_response_fault_r;
        status_out_r[8] <= clamp_active_r;
        status_out_r[9] <= fallback_active_r;
        status_out_r[15:10] <= last_error_code_r;
    end
end

endmodule
