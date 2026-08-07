module motor_control_top (
    input clk_rst_n,
    input req_stream_valid,
    output req_stream_ready,
    input [127:0] req_stream_data,
    output rsp_stream_valid,
    input rsp_stream_ready,
    output [127:0] rsp_stream_data,
    input [5:0] csr_if_addr,
    input [63:0] csr_if_wdata,
    output [63:0] csr_if_rdata,
    input csr_if_we,
    input csr_if_re,
    input csr_if_valid,
    output csr_if_ready,
    output [31:0] actuator_cmd,
    output actuator_valid,
    input service_busy,
    input service_done,
    input service_error
);
    wire accepted_req;
    wire rejected_req;
    wire stale_req;
    wire [15:0] request_id_dec;
    wire [3:0] protocol_version_dec;
    wire [3:0] request_type_dec;
    wire [7:0] service_selector_dec;
    wire [15:0] geometry_handle_dec;
    wire [7:0] velocity_dec;
    wire [7:0] flags_dec;
    wire dispatch_req;
    wire [15:0] dispatch_request_id;
    wire [7:0] dispatch_status;
    wire [15:0] dispatch_geometry_handle;
    wire [7:0] dispatch_velocity_meta;
    wire timeout_active;
    wire timeout_expired;
    wire [15:0] latest_request_id;
    wire busy_flag;
    wire fsm_error;
    wire [15:0] timeout_limit_cfg;
    wire fifo_enable_cfg;
    wire [31:0] clamp_min_cfg;
    wire [31:0] clamp_max_cfg;
    wire [3:0] protocol_version_cfg;
    wire [3:0] request_type_mask_cfg;
    wire diagnostic_reject_only_cfg;
    wire [31:0] fallback_code_cfg;
    wire [31:0] neutral_code_cfg;
    wire [15:0] csr_status;
    wire [31:0] sanitized_cmd;
    wire sanitized_valid;
    wire [31:0] safe_cmd;
    wire safe_valid;
    wire fallback_active;
    wire sanitized_accepted;
    wire sanitized_stale;
    wire sanitized_timeout;
    wire sanitized_fallback;
    wire sanitized_error;

    request_validation_unit u_request_validation_unit (
        .clk_rst_n(clk_rst_n),
        .req_stream_valid(req_stream_valid),
        .req_stream_data(req_stream_data),
        .accepted_o(accepted_req),
        .rejected_o(rejected_req),
        .stale_o(stale_req),
        .request_id_o(request_id_dec),
        .protocol_version_o(protocol_version_dec),
        .request_type_o(request_type_dec),
        .service_selector_o(service_selector_dec),
        .geometry_handle_o(geometry_handle_dec),
        .stream_velocity_mps_o(velocity_dec),
        .flags_o(flags_dec)
    );

    transport_dispatch_fsm u_transport_dispatch_fsm (
        .clk_rst_n(clk_rst_n),
        .accepted_i(accepted_req),
        .rejected_i(rejected_req),
        .stale_i(stale_req),
        .request_id_i(request_id_dec),
        .service_selector_i(service_selector_dec),
        .geometry_handle_i(geometry_handle_dec),
        .velocity_i(velocity_dec),
        .flags_i(flags_dec),
        .service_busy_i(service_busy),
        .service_done_i(service_done),
        .service_error_i(service_error),
        .timeout_limit_i(timeout_limit_cfg),
        .fifo_enable_i(fifo_enable_cfg),
        .dispatch_req_o(dispatch_req),
        .dispatch_request_id_o(dispatch_request_id),
        .dispatch_service_selector_o(),
        .dispatch_geometry_handle_o(dispatch_geometry_handle),
        .dispatch_velocity_o(dispatch_velocity_meta),
        .dispatch_flags_o(dispatch_status),
        .timeout_active_o(timeout_active),
        .timeout_expired_o(timeout_expired),
        .latest_request_id_o(latest_request_id),
        .busy_o(busy_flag),
        .error_o(fsm_error)
    );

    response_sanitizer u_response_sanitizer (
        .clk_rst_n(clk_rst_n),
        .resp_valid_i(dispatch_req),
        .resp_request_id_i(dispatch_request_id),
        .resp_status_i(dispatch_status),
        .resp_actuator_cmd_i(sanitized_cmd),
        .resp_fallback_i(fallback_active),
        .latest_request_id_i(latest_request_id),
        .timeout_expired_i(timeout_expired),
        .service_error_i(fsm_error),
        .clamp_min_i(clamp_min_cfg),
        .clamp_max_i(clamp_max_cfg),
        .sanitized_valid_o(sanitized_valid),
        .sanitized_cmd_o(sanitized_cmd),
        .accepted_o(sanitized_accepted),
        .stale_o(sanitized_stale),
        .timeout_o(sanitized_timeout),
        .fallback_o(sanitized_fallback),
        .error_o(sanitized_error)
    );

    safe_fallback_controller u_safe_fallback_controller (
        .clk_rst_n(clk_rst_n),
        .fallback_enable_i(fifo_enable_cfg),
        .fallback_code_i(fallback_code_cfg),
        .neutral_code_i(neutral_code_cfg),
        .error_i(fsm_error),
        .timeout_i(timeout_expired),
        .stale_i(stale_req),
        .rejected_i(rejected_req),
        .service_busy_i(busy_flag),
        .safe_cmd_o(safe_cmd),
        .safe_valid_o(safe_valid),
        .fallback_active_o(fallback_active)
    );

    csr_window_ctrl u_csr_window_ctrl (
        .clk_rst_n(clk_rst_n),
        .csr_if_addr(csr_if_addr),
        .csr_if_wdata(csr_if_wdata),
        .csr_if_rdata(csr_if_rdata),
        .csr_if_we(csr_if_we),
        .csr_if_re(csr_if_re),
        .csr_if_valid(csr_if_valid),
        .csr_if_ready(csr_if_ready),
        .timeout_limit_o(timeout_limit_cfg),
        .clamp_min_o(clamp_min_cfg),
        .clamp_max_o(clamp_max_cfg),
        .protocol_version_exp_o(protocol_version_cfg),
        .request_type_mask_o(request_type_mask_cfg),
        .diagnostic_reject_only_o(diagnostic_reject_only_cfg),
        .fifo_enable_o(fifo_enable_cfg),
        .fallback_code_o(fallback_code_cfg),
        .neutral_code_o(neutral_code_cfg),
        .status_o(csr_status)
    );

    assign req_stream_ready = 1'b1;
    assign rsp_stream_valid = sanitized_valid | sanitized_stale | sanitized_timeout | sanitized_fallback | sanitized_error;
    assign rsp_stream_data = {112'h0, csr_status};
    assign actuator_cmd = sanitized_valid ? sanitized_cmd : safe_cmd;
    assign actuator_valid = sanitized_valid | safe_valid;
endmodule
