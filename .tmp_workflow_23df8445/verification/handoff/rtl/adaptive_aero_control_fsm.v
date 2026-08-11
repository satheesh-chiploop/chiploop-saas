module adaptive_aero_control_fsm (
    clk,
    rst_n,
    enable,
    clear_faults,
    mode_select,
    fault_status_in,
    req_issued,
    rsp_accepted,
    rsp_malformed,
    rsp_stale,
    rsp_seq_mismatch,
    rsp_duplicate,
    outstanding_timer_expired,
    service_unavailable,
    candidate_valid,
    candidate_invalid,
    candidate_fallback,
    idle_safe,
    issue_request,
    validate_response,
    apply_command,
    enter_fallback,
    latch_fault,
    fsm_state,
    fault_status_out
);
    input clk;
    input rst_n;
    input enable;
    input clear_faults;
    input [2:0] mode_select;
    input [15:0] fault_status_in;
    input req_issued;
    input rsp_accepted;
    input rsp_malformed;
    input rsp_stale;
    input rsp_seq_mismatch;
    input rsp_duplicate;
    input outstanding_timer_expired;
    input service_unavailable;
    input candidate_valid;
    input candidate_invalid;
    input candidate_fallback;
    output idle_safe;
    output issue_request;
    output validate_response;
    output apply_command;
    output enter_fallback;
    output latch_fault;
    output [2:0] fsm_state;
    output [15:0] fault_status_out;
    localparam S_RESET = 3'd0;
    localparam S_IDLE = 3'd1;
    localparam S_ISSUE_REQ = 3'd2;
    localparam S_WAIT_RSP = 3'd3;
    localparam S_VALIDATE = 3'd4;
    localparam S_APPLY_CMD = 3'd5;
    localparam S_FALLBACK = 3'd6;
    localparam S_FAULT_LATCH = 3'd7;

    reg [2:0] state_r, state_n;
    reg idle_safe_r;
    reg issue_request_r;
    reg validate_response_r;
    reg apply_command_r;
    reg enter_fallback_r;
    reg latch_fault_r;
    reg [15:0] fault_status_r;
    assign idle_safe = idle_safe_r;
    assign issue_request = issue_request_r;
    assign validate_response = validate_response_r;
    assign apply_command = apply_command_r;
    assign enter_fallback = enter_fallback_r;
    assign latch_fault = latch_fault_r;
    assign fsm_state = state_r;
    assign fault_status_out = fault_status_r;

    always @(*) begin
        state_n = state_r;
        idle_safe_r = 1'b0;
        issue_request_r = 1'b0;
        validate_response_r = 1'b0;
        apply_command_r = 1'b0;
        enter_fallback_r = 1'b0;
        latch_fault_r = 1'b0;
        case (state_r)
            S_RESET: begin
                idle_safe_r = 1'b1;
                state_n = S_IDLE;
            end
            S_IDLE: begin
                idle_safe_r = 1'b1;
                if (clear_faults && (fault_status_in == 16'h0000)) begin
                    state_n = S_IDLE;
                end else if (enable) begin
                    issue_request_r = 1'b1;
                    state_n = S_ISSUE_REQ;
                end
            end
            S_ISSUE_REQ: begin
                issue_request_r = 1'b1;
                state_n = S_WAIT_RSP;
            end
            S_WAIT_RSP: begin
                if (outstanding_timer_expired || rsp_malformed || rsp_stale || rsp_seq_mismatch || rsp_duplicate || service_unavailable) begin
                    enter_fallback_r = 1'b1;
                    latch_fault_r = 1'b1;
                    state_n = S_FAULT_LATCH;
                end else if (rsp_accepted) begin
                    state_n = S_VALIDATE;
                end
            end
            S_VALIDATE: begin
                validate_response_r = 1'b1;
                if (candidate_invalid) begin
                    enter_fallback_r = 1'b1;
                    state_n = S_FALLBACK;
                end else if (candidate_valid) begin
                    apply_command_r = 1'b1;
                    state_n = S_APPLY_CMD;
                end else if (candidate_fallback) begin
                    enter_fallback_r = 1'b1;
                    state_n = S_FALLBACK;
                end
            end
            S_APPLY_CMD: begin
                apply_command_r = 1'b1;
                state_n = S_IDLE;
            end
            S_FALLBACK: begin
                enter_fallback_r = 1'b1;
                latch_fault_r = 1'b1;
                state_n = S_FAULT_LATCH;
            end
            S_FAULT_LATCH: begin
                latch_fault_r = 1'b1;
                if (clear_faults && idle_safe_r) begin
                    state_n = S_IDLE;
                end
            end
            default: begin
                state_n = S_RESET;
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_r <= S_RESET;
            fault_status_r <= 16'h0001;
        end else begin
            state_r <= state_n;
            if (rsp_malformed) fault_status_r[0] <= 1'b1;
            if (rsp_stale) fault_status_r[1] <= 1'b1;
            if (rsp_seq_mismatch || rsp_duplicate) fault_status_r[2] <= 1'b1;
            if (outstanding_timer_expired) fault_status_r[3] <= 1'b1;
            if (service_unavailable) fault_status_r[4] <= 1'b1;
            if (candidate_invalid) fault_status_r[5] <= 1'b1;
            if (candidate_fallback) fault_status_r[6] <= 1'b1;
            if (clear_faults && idle_safe_r) fault_status_r <= 16'h0000;
            if (fault_status_in != 16'h0000) fault_status_r <= fault_status_r | fault_status_in;
        end
    end
endmodule
