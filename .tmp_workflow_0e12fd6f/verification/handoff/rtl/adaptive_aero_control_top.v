module adaptive_aero_control_top (
    clk,
    rst_n,
    s_axis_req_data,
    s_axis_req_valid,
    s_axis_req_ready,
    m_axis_resp_data,
    m_axis_resp_valid,
    m_axis_resp_ready,
    m_axis_act_data,
    m_axis_act_valid,
    m_axis_act_ready,
    csr_addr_data,
    csr_wr_en,
    csr_wr_data,
    csr_rd_data,
    csr_rd_valid,
    mem_dout,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    resp_record_seq,
    resp_record_status,
    resp_record_freshness,
    resp_record_complete,
    resp_record_ctrl_result,
    resp_record_valid,
    cmd_raw_data,
    cmd_raw_valid
);
    input         clk;
    input         rst_n;
    input  [127:0] s_axis_req_data;
    input         s_axis_req_valid;
    output        s_axis_req_ready;
    output [127:0] m_axis_resp_data;
    output        m_axis_resp_valid;
    input         m_axis_resp_ready;
    output [63:0] m_axis_act_data;
    output        m_axis_act_valid;
    input         m_axis_act_ready;
    input  [63:0] csr_addr_data;
    input         csr_wr_en;
    input  [63:0] csr_wr_data;
    output [63:0] csr_rd_data;
    output        csr_rd_valid;
    input  [127:0] mem_dout;
    input         model_req_ready;
    input         model_rsp_valid;
    input  [127:0] model_rsp_data;
    input  [31:0] resp_record_seq;
    input  [3:0] resp_record_status;
    input  [3:0] resp_record_freshness;
    input         resp_record_complete;
    input  [15:0] resp_record_ctrl_result;
    input         resp_record_valid;
    input  [63:0] cmd_raw_data;
    input         cmd_raw_valid;
wire cfg_enable;
wire cfg_soft_clear_faults;
wire cfg_force_inhibit;
wire cfg_queue_depth_enable;
wire cfg_response_accept_enable;
wire [31:0] cfg_timeout_cycles;
wire [15:0] cfg_max_actuator_cmd;
wire [15:0] cfg_min_actuator_cmd;
wire [15:0] cfg_rate_limit_step;
wire status_busy;
wire status_response_valid_seen;
wire status_stale_fault;
wire status_timeout_fault;
wire status_protocol_fault;
wire status_fallback_active;
wire status_request_pending;
wire status_response_accepted;
wire [31:0] status_timeout_count;
wire [31:0] status_stale_reject_count;
wire [31:0] status_fallback_activation_count;
wire [31:0] status_last_seq_accepted;
wire [31:0] status_last_seq_rejected;
wire req_fifo_push_valid;
wire [127:0] req_fifo_push_data;
wire req_fifo_push_ready;
wire req_fifo_pop_valid;
wire [127:0] req_fifo_pop_data;
wire req_fifo_pop_ready;
    wire [31:0] req_record_seq;
    wire [3:0] req_record_mode;
    wire [15:0] req_record_geom_token;
    wire [15:0] req_record_flow_speed;
    wire [11:0] req_record_flow_alpha;
    wire [11:0] req_record_flow_beta;
    wire req_record_valid;

    wire [63:0] cmd_clamped_data;
    wire cmd_clamped_valid;
    wire [31:0] active_seq;
    wire [2:0] fsm_state;

    adaptive_aero_req_fifo_wrapper u_req_fifo (
        .clk(clk),
        .rst_n(rst_n),
        .push_valid(req_fifo_push_valid),
        .push_data(req_fifo_push_data),
        .push_ready(req_fifo_push_ready),
        .pop_valid(req_fifo_pop_valid),
        .pop_data(req_fifo_pop_data),
        .pop_ready(req_fifo_pop_ready),
        .level(),
        .mem_we(),
        .mem_addr(),
        .mem_din(),
        .mem_dout(mem_dout)
    );

    adaptive_aero_csr_decode u_csr_decode (
        .clk(clk),
        .rst_n(rst_n),
        .csr_addr_data(csr_addr_data),
        .csr_wr_en(csr_wr_en),
        .csr_wr_data(csr_wr_data),
        .csr_rd_data(csr_rd_data),
        .csr_rd_valid(csr_rd_valid),
        .cfg_enable(cfg_enable),
        .cfg_soft_clear_faults(cfg_soft_clear_faults),
        .cfg_force_inhibit(cfg_force_inhibit),
        .cfg_queue_depth_enable(cfg_queue_depth_enable),
        .cfg_response_accept_enable(cfg_response_accept_enable),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_max_actuator_cmd(cfg_max_actuator_cmd),
        .cfg_min_actuator_cmd(cfg_min_actuator_cmd),
        .cfg_rate_limit_step(cfg_rate_limit_step),
        .status_busy(status_busy),
        .status_response_valid_seen(status_response_valid_seen),
        .status_stale_fault(status_stale_fault),
        .status_timeout_fault(status_timeout_fault),
        .status_protocol_fault(status_protocol_fault),
        .status_fallback_active(status_fallback_active),
        .status_request_pending(status_request_pending),
        .status_response_accepted(status_response_accepted),
        .status_timeout_count(status_timeout_count),
        .status_stale_reject_count(status_stale_reject_count),
        .status_fallback_activation_count(status_fallback_activation_count),
        .status_last_seq_accepted(status_last_seq_accepted),
        .status_last_seq_rejected(status_last_seq_rejected)
    );

    adaptive_aero_transport_ctrl u_transport_ctrl (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_enable(cfg_enable),
        .cfg_soft_clear_faults(cfg_soft_clear_faults),
        .cfg_force_inhibit(cfg_force_inhibit),
        .cfg_queue_depth_enable(cfg_queue_depth_enable),
        .cfg_response_accept_enable(cfg_response_accept_enable),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_max_actuator_cmd(cfg_max_actuator_cmd),
        .cfg_min_actuator_cmd(cfg_min_actuator_cmd),
        .cfg_rate_limit_step(cfg_rate_limit_step),
        .s_axis_req_data(s_axis_req_data),
        .s_axis_req_valid(s_axis_req_valid),
        .s_axis_req_ready(s_axis_req_ready),
        .m_axis_resp_data(m_axis_resp_data),
        .m_axis_resp_valid(m_axis_resp_valid),
        .m_axis_resp_ready(m_axis_resp_ready),
        .m_axis_act_data(m_axis_act_data),
        .m_axis_act_valid(m_axis_act_valid),
        .m_axis_act_ready(m_axis_act_ready),
        .model_req_valid(),
        .model_req_data(),
        .model_req_ready(model_req_ready),
        .model_rsp_valid(model_rsp_valid),
        .model_rsp_data(model_rsp_data),
        .model_rsp_ready(),
        .req_fifo_push_valid(req_fifo_push_valid),
        .req_fifo_push_data(req_fifo_push_data),
        .req_fifo_push_ready(req_fifo_push_ready),
        .req_fifo_pop_valid(req_fifo_pop_valid),
        .req_fifo_pop_data(req_fifo_pop_data),
        .req_fifo_pop_ready(req_fifo_pop_ready),
        .req_record_seq(req_record_seq),
        .req_record_mode(req_record_mode),
        .req_record_geom_token(req_record_geom_token),
        .req_record_flow_speed(req_record_flow_speed),
        .req_record_flow_alpha(req_record_flow_alpha),
        .req_record_flow_beta(req_record_flow_beta),
        .req_record_valid(req_record_valid),
        .resp_record_seq(resp_record_seq),
        .resp_record_status(resp_record_status),
        .resp_record_freshness(resp_record_freshness),
        .resp_record_complete(resp_record_complete),
        .resp_record_ctrl_result(resp_record_ctrl_result),
        .resp_record_valid(resp_record_valid),
        .cmd_raw_data(cmd_raw_data),
        .cmd_raw_valid(cmd_raw_valid),
        .cmd_clamped_data(cmd_clamped_data),
        .cmd_clamped_valid(cmd_clamped_valid),
        .status_busy(status_busy),
        .status_response_valid_seen(status_response_valid_seen),
        .status_stale_fault(status_stale_fault),
        .status_timeout_fault(status_timeout_fault),
        .status_protocol_fault(status_protocol_fault),
        .status_fallback_active(status_fallback_active),
        .status_request_pending(status_request_pending),
        .status_response_accepted(status_response_accepted),
        .status_timeout_count(status_timeout_count),
        .status_stale_reject_count(status_stale_reject_count),
        .status_fallback_activation_count(status_fallback_activation_count),
        .status_last_seq_accepted(status_last_seq_accepted),
        .status_last_seq_rejected(status_last_seq_rejected),
        .active_seq(active_seq),
        .fsm_state(fsm_state)
    );
endmodule
