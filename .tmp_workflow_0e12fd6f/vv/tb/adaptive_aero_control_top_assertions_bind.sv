/*
 * Auto-generated SVA bind file.
 * Uses only spec-declared signals.
 */
bind adaptive_aero_control_top adaptive_aero_control_top_assertions u_adaptive_aero_control_top_assertions (
  .clk(clk),
  .rst_n(rst_n),
  .s_axis_req_data(s_axis_req_data),
  .s_axis_req_valid(s_axis_req_valid),
  .s_axis_req_ready(s_axis_req_ready),
  .m_axis_resp_data(m_axis_resp_data),
  .m_axis_resp_valid(m_axis_resp_valid),
  .m_axis_resp_ready(m_axis_resp_ready),
  .m_axis_act_data(m_axis_act_data),
  .m_axis_act_valid(m_axis_act_valid),
  .m_axis_act_ready(m_axis_act_ready),
  .csr_addr_data(csr_addr_data),
  .csr_wr_en(csr_wr_en),
  .csr_wr_data(csr_wr_data),
  .csr_rd_data(csr_rd_data),
  .csr_rd_valid(csr_rd_valid),
  .mem_dout(mem_dout),
  .model_req_ready(model_req_ready),
  .model_rsp_valid(model_rsp_valid),
  .model_rsp_data(model_rsp_data),
  .resp_record_seq(resp_record_seq),
  .resp_record_status(resp_record_status),
  .resp_record_freshness(resp_record_freshness),
  .resp_record_complete(resp_record_complete),
  .resp_record_ctrl_result(resp_record_ctrl_result),
  .resp_record_valid(resp_record_valid),
  .cmd_raw_data(cmd_raw_data),
  .cmd_raw_valid(cmd_raw_valid)
);
