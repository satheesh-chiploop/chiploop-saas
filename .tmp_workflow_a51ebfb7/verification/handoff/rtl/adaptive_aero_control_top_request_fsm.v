module adaptive_aero_control_top_request_fsm (
    clk,
    reset_n,
    cfg_request_issue,
    cfg_allow_multi_outstanding,
    cfg_request_id,
    cfg_geometry_handle,
    cfg_flow_handle,
    cfg_timestamp,
    cfg_command_mode,
    cfg_status_flags,
    cfg_timeout_cycles,
    cfg_force_safe_mode,
    cfg_oper_en_min,
    cfg_oper_en_max,
    model_req_desc_o,
    model_req_valid_o,
    model_req_ready_i,
    model_rsp_desc_i,
    model_rsp_valid_i,
    model_rsp_ready_o,
    reg_state,
    reg_fault_summary,
    reg_outstanding_req_id,
    reg_response_req_id,
    reg_pending,
    reg_response_received,
    reg_stale_reject,
    reg_timeout_expired,
    reg_envelope_violation,
    reg_service_error,
    reg_fallback_active,
    reg_irq_pulse,
    selected_cmd_o,
    selected_cmd_valid_o
);

input clk;
input reset_n;
input cfg_request_issue;
input cfg_allow_multi_outstanding;
input [7:0] cfg_request_id;
input [15:0] cfg_geometry_handle;
input [15:0] cfg_flow_handle;
input [31:0] cfg_timestamp;
input [3:0] cfg_command_mode;
input [7:0] cfg_status_flags;
input [31:0] cfg_timeout_cycles;
input cfg_force_safe_mode;
input [15:0] cfg_oper_en_min;
input [15:0] cfg_oper_en_max;
output [63:0] model_req_desc_o;
output model_req_valid_o;
input model_req_ready_i;
input [63:0] model_rsp_desc_i;
input model_rsp_valid_i;
output model_rsp_ready_o;
output [7:0] reg_state;
output [15:0] reg_fault_summary;
output [7:0] reg_outstanding_req_id;
output [7:0] reg_response_req_id;
output reg_pending;
output reg_response_received;
output reg_stale_reject;
output reg_timeout_expired;
output reg_envelope_violation;
output reg_service_error;
output reg_fallback_active;
output reg_irq_pulse;
output [15:0] selected_cmd_o;
output selected_cmd_valid_o;

localparam ST_IDLE = 8'h00;
localparam ST_WAIT = 8'h01;
localparam ST_RESP = 8'h02;
localparam ST_SAFE = 8'h03;

reg [7:0] state_r;
reg [7:0] outstanding_req_id_r;
reg [7:0] response_req_id_r;
reg pending_r;
reg response_received_r;
reg stale_reject_r;
reg timeout_expired_r;
reg envelope_violation_r;
reg service_error_r;
reg fallback_active_r;
reg irq_pulse_r;
reg [15:0] selected_cmd_r;
reg selected_cmd_valid_r;
reg [31:0] age_counter_r;
reg [15:0] fault_summary_r;
reg [63:0] model_req_desc_r;
reg model_req_valid_r;
reg model_rsp_ready_r;
reg [15:0] selected_cmd_next;
reg selected_cmd_valid_next;
reg [7:0] next_state;
reg [7:0] next_outstanding_req_id;
reg [7:0] next_response_req_id;
reg next_pending;
reg next_response_received;
reg next_stale_reject;
reg next_timeout_expired;
reg next_envelope_violation;
reg next_service_error;
reg next_fallback_active;
reg next_irq_pulse;
reg [31:0] next_age_counter;
reg [15:0] next_fault_summary;
reg [63:0] req_desc_comb;
reg [15:0] cmd_raw;
reg envelope_bad;
reg timeout_bad;
reg id_match;
reg response_ok;
reg issue_req;

assign model_req_desc_o = model_req_desc_r;
assign model_req_valid_o = model_req_valid_r;
assign model_rsp_ready_o = model_rsp_ready_r;
assign reg_state = state_r;
assign reg_fault_summary = fault_summary_r;
assign reg_outstanding_req_id = outstanding_req_id_r;
assign reg_response_req_id = response_req_id_r;
assign reg_pending = pending_r;
assign reg_response_received = response_received_r;
assign reg_stale_reject = stale_reject_r;
assign reg_timeout_expired = timeout_expired_r;
assign reg_envelope_violation = envelope_violation_r;
assign reg_service_error = service_error_r;
assign reg_fallback_active = fallback_active_r;
assign reg_irq_pulse = irq_pulse_r;
assign selected_cmd_o = selected_cmd_r;
assign selected_cmd_valid_o = selected_cmd_valid_r;

always @(*) begin
    next_state = state_r;
    next_outstanding_req_id = outstanding_req_id_r;
    next_response_req_id = response_req_id_r;
    next_pending = pending_r;
    next_response_received = 1'b0;
    next_stale_reject = 1'b0;
    next_timeout_expired = timeout_expired_r;
    next_envelope_violation = 1'b0;
    next_service_error = 1'b0;
    next_fallback_active = fallback_active_r;
    next_irq_pulse = 1'b0;
    next_age_counter = age_counter_r;
    next_fault_summary = fault_summary_r;
    selected_cmd_next = selected_cmd_r;
    selected_cmd_valid_next = 1'b0;
    req_desc_comb = {8'b0, cfg_timestamp[31:0], cfg_geometry_handle[15:8], cfg_flow_handle[15:8], cfg_request_id[7:0]};
    cmd_raw = {cfg_oper_en_min[7:0], cfg_oper_en_max[7:0]};
    envelope_bad = (cfg_oper_en_min > cfg_oper_en_max);
    timeout_bad = 1'b0;
    id_match = 1'b0;
    response_ok = 1'b0;
    issue_req = cfg_request_issue;

    if (state_r == ST_WAIT) begin
        next_age_counter = age_counter_r + 32'h00000001;
        if ((cfg_timeout_cycles != 32'h00000000) && (age_counter_r >= cfg_timeout_cycles)) begin
            timeout_bad = 1'b1;
            next_timeout_expired = 1'b1;
            next_fallback_active = 1'b1;
            next_irq_pulse = 1'b1;
            next_state = ST_SAFE;
            next_pending = 1'b0;
            next_fault_summary[0] = 1'b1;
        end
    end

    if (cfg_force_safe_mode) begin
        next_fallback_active = 1'b1;
        next_irq_pulse = 1'b1;
        next_state = ST_SAFE;
        next_pending = 1'b0;
        next_fault_summary[3] = 1'b1;
    end

    if (envelope_bad) begin
        next_envelope_violation = 1'b1;
        next_fallback_active = 1'b1;
        next_state = ST_SAFE;
        next_pending = 1'b0;
        next_irq_pulse = 1'b1;
        next_fault_summary[2] = 1'b1;
    end

    if (model_rsp_valid_i) begin
        next_response_req_id = model_rsp_desc_i[7:0];
        id_match = (model_rsp_desc_i[7:0] == outstanding_req_id_r);
        response_ok = id_match && !timeout_bad && !envelope_bad && !cfg_force_safe_mode;
        next_response_received = response_ok;
        if (response_ok) begin
            next_state = ST_RESP;
            next_pending = 1'b0;
            selected_cmd_next = model_rsp_desc_i[31:16];
            selected_cmd_valid_next = 1'b1;
            next_irq_pulse = 1'b1;
            next_fault_summary = 16'h0000;
            next_age_counter = 32'h00000000;
        end else begin
            next_stale_reject = 1'b1;
            next_service_error = 1'b1;
            next_fallback_active = 1'b1;
            next_state = ST_SAFE;
            next_pending = 1'b0;
            next_irq_pulse = 1'b1;
            next_fault_summary[1] = 1'b1;
            next_fault_summary[4] = 1'b1;
        end
    end

    if (cfg_request_issue && !pending_r && !cfg_force_safe_mode && !envelope_bad) begin
        next_outstanding_req_id = cfg_request_id;
        next_pending = 1'b1;
        next_state = ST_WAIT;
        next_age_counter = 32'h00000000;
    end else begin
    end

    if (pending_r) begin
    end

    if (next_state == ST_SAFE) begin
        selected_cmd_valid_next = 1'b0;
        selected_cmd_next = 16'h0000;
    end

    if (next_state == ST_RESP) begin
        next_state = ST_IDLE;
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        state_r <= ST_IDLE;
        outstanding_req_id_r <= 8'h00;
        response_req_id_r <= 8'h00;
        pending_r <= 1'b0;
        response_received_r <= 1'b0;
        stale_reject_r <= 1'b0;
        timeout_expired_r <= 1'b0;
        envelope_violation_r <= 1'b0;
        service_error_r <= 1'b0;
        fallback_active_r <= 1'b0;
        irq_pulse_r <= 1'b0;
        selected_cmd_r <= 16'h0000;
        selected_cmd_valid_r <= 1'b0;
        age_counter_r <= 32'h00000000;
        fault_summary_r <= 16'h0000;
        model_req_desc_r <= 64'h0000000000000000;
        model_req_valid_r <= 1'b0;
        model_rsp_ready_r <= 1'b1;
    end else begin
        state_r <= next_state;
        outstanding_req_id_r <= next_outstanding_req_id;
        response_req_id_r <= next_response_req_id;
        pending_r <= next_pending;
        response_received_r <= next_response_received;
        stale_reject_r <= next_stale_reject;
        timeout_expired_r <= next_timeout_expired;
        envelope_violation_r <= next_envelope_violation;
        service_error_r <= next_service_error;
        fallback_active_r <= next_fallback_active;
        irq_pulse_r <= next_irq_pulse;
        selected_cmd_r <= selected_cmd_next;
        selected_cmd_valid_r <= selected_cmd_valid_next;
        age_counter_r <= next_age_counter;
        fault_summary_r <= next_fault_summary;
        model_req_desc_r <= req_desc_comb;
        model_req_valid_r <= model_req_valid_r;
        model_rsp_ready_r <= model_rsp_ready_r;
    end
end

endmodule
