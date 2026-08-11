module adaptive_aero_control_top (
    clk,
    rst_n,
    cfg_wr_en,
    cfg_rd_en,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    req_stream_valid,
    req_stream_ready,
    req_stream_data,
    rsp_stream_valid,
    rsp_stream_ready,
    rsp_stream_data,
    actuator_cmd_valid,
    actuator_cmd_ready,
    actuator_cmd_data
);
    input clk;
    input rst_n;
    input cfg_wr_en;
    input cfg_rd_en;
    input [5:0] cfg_addr;
    input [63:0] cfg_wdata;
    output [63:0] cfg_rdata;
    output req_stream_valid;
    input req_stream_ready;
    output [127:0] req_stream_data;
    input rsp_stream_valid;
    output rsp_stream_ready;
    input [127:0] rsp_stream_data;
    output actuator_cmd_valid;
    input actuator_cmd_ready;
    output [31:0] actuator_cmd_data;
wire enable;
wire clear_faults;
wire [2:0] mode_select;
wire [7:0] freshness_limit;
wire [7:0] timeout_limit;
wire [15:0] max_cmd;
wire [15:0] min_cmd;
wire [15:0] rate_limit;
wire [3:0] fallback_mode;
wire [15:0] sequence_counter;
wire [15:0] fault_status;
wire idle_safe;
wire req_issued;
wire [15:0] req_seq;
    wire [7:0] req_age_tag;
    wire [31:0] req_metadata;
    wire [15:0] req_handle;
wire rsp_accepted;
wire [15:0] rsp_seq;
wire [7:0] rsp_age_tag;
wire [31:0] rsp_metadata;
wire [15:0] rsp_handle;
wire rsp_malformed;
wire rsp_stale;
wire rsp_seq_mismatch;
wire rsp_duplicate;
    wire outstanding_valid;
    wire [15:0] outstanding_seq;
    wire [7:0] outstanding_age;
wire outstanding_timer_expired;
wire transport_fault;
wire [15:0] candidate_cmd;
wire candidate_valid;
wire candidate_fallback;
wire candidate_invalid;
    wire [15:0] cmd_bounded;
wire cmd_valid;
    wire cmd_clamped_low;
    wire cmd_clamped_high;
    wire rate_limited;
wire service_unavailable;
    wire fallback_selected;
    wire issue_request;
    wire validate_response;
    wire apply_command;
    wire enter_fallback;
    wire latch_fault;
    wire [2:0] fsm_state;

    adaptive_aero_control_csr u_csr (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_wr_en(cfg_wr_en),
        .cfg_rd_en(cfg_rd_en),
        .cfg_addr(cfg_addr),
        .cfg_wdata(cfg_wdata),
        .cfg_rdata(cfg_rdata),
        .enable(enable),
        .clear_faults(clear_faults),
        .mode_select(mode_select),
        .freshness_limit(freshness_limit),
        .timeout_limit(timeout_limit),
        .max_cmd(max_cmd),
        .min_cmd(min_cmd),
        .rate_limit(rate_limit),
        .fallback_mode(fallback_mode),
        .sequence_counter(sequence_counter),
        .fault_status(fault_status),
        .idle_safe(idle_safe)
    );

    adaptive_aero_control_transport u_transport (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .mode_select(mode_select),
        .freshness_limit(freshness_limit),
        .timeout_limit(timeout_limit),
        .sequence_counter(sequence_counter),
        .req_stream_valid(req_stream_valid),
        .req_stream_ready(req_stream_ready),
        .req_stream_data(req_stream_data),
        .rsp_stream_valid(rsp_stream_valid),
        .rsp_stream_ready(rsp_stream_ready),
        .rsp_stream_data(rsp_stream_data),
        .req_issued(req_issued),
        .req_seq(req_seq),
        .req_age_tag(req_age_tag),
        .req_metadata(req_metadata),
        .req_handle(req_handle),
        .rsp_accepted(rsp_accepted),
        .rsp_seq(rsp_seq),
        .rsp_age_tag(rsp_age_tag),
        .rsp_metadata(rsp_metadata),
        .rsp_handle(rsp_handle),
        .rsp_malformed(rsp_malformed),
        .rsp_stale(rsp_stale),
        .rsp_seq_mismatch(rsp_seq_mismatch),
        .rsp_duplicate(rsp_duplicate),
        .outstanding_valid(outstanding_valid),
        .outstanding_seq(outstanding_seq),
        .outstanding_age(outstanding_age),
        .outstanding_timer_expired(outstanding_timer_expired),
        .transport_fault(transport_fault)
    );

    adaptive_aero_control_validator u_validator (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .mode_select(mode_select),
        .max_cmd(max_cmd),
        .min_cmd(min_cmd),
        .rate_limit(rate_limit),
        .fallback_mode(fallback_mode),
        .rsp_accepted(rsp_accepted),
        .rsp_seq(rsp_seq),
        .rsp_age_tag(rsp_age_tag),
        .rsp_metadata(rsp_metadata),
        .rsp_handle(rsp_handle),
        .rsp_malformed(rsp_malformed),
        .rsp_stale(rsp_stale),
        .rsp_seq_mismatch(rsp_seq_mismatch),
        .rsp_duplicate(rsp_duplicate),
        .outstanding_timer_expired(outstanding_timer_expired),
        .transport_fault(transport_fault),
        .candidate_cmd(candidate_cmd),
        .candidate_valid(candidate_valid),
        .candidate_fallback(candidate_fallback),
        .candidate_invalid(candidate_invalid),
        .cmd_bounded(cmd_bounded),
        .cmd_valid(cmd_valid),
        .cmd_clamped_low(cmd_clamped_low),
        .cmd_clamped_high(cmd_clamped_high),
        .rate_limited(rate_limited),
        .service_unavailable(service_unavailable),
        .fallback_selected(fallback_selected)
    );

    adaptive_aero_control_fsm u_fsm (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .clear_faults(clear_faults),
        .mode_select(mode_select),
        .fault_status_in(fault_status),
        .req_issued(req_issued),
        .rsp_accepted(rsp_accepted),
        .rsp_malformed(rsp_malformed),
        .rsp_stale(rsp_stale),
        .rsp_seq_mismatch(rsp_seq_mismatch),
        .rsp_duplicate(rsp_duplicate),
        .outstanding_timer_expired(outstanding_timer_expired),
        .service_unavailable(service_unavailable),
        .candidate_valid(candidate_valid),
        .candidate_invalid(candidate_invalid),
        .candidate_fallback(candidate_fallback),
        .idle_safe(idle_safe),
        .issue_request(issue_request),
        .validate_response(validate_response),
        .apply_command(apply_command),
        .enter_fallback(enter_fallback),
        .latch_fault(latch_fault),
        .fsm_state(fsm_state),
        .fault_status_out(fault_status)
    );

    assign actuator_cmd_valid = cmd_valid & (apply_command | candidate_fallback | fallback_selected);
    assign actuator_cmd_data = {16'h0000, candidate_cmd};

endmodule
