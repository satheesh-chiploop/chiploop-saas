/*
 * Auto-generated SVA scaffold.
 * Derived from spec_json / digital_spec_json.
 * No hardcoded design-specific signal assumptions.
 */

module adaptive_aero_control_top_assertions (
  input logic clk,
  input logic [63:0] cmd_raw_data,
  input logic cmd_raw_valid,
  input logic [63:0] csr_addr_data,
  input logic [63:0] csr_rd_data,
  input logic csr_rd_valid,
  input logic [63:0] csr_wr_data,
  input logic csr_wr_en,
  input logic [63:0] m_axis_act_data,
  input logic m_axis_act_ready,
  input logic m_axis_act_valid,
  input logic [127:0] m_axis_resp_data,
  input logic m_axis_resp_ready,
  input logic m_axis_resp_valid,
  input logic [127:0] mem_dout,
  input logic model_req_ready,
  input logic [127:0] model_rsp_data,
  input logic model_rsp_valid,
  input logic resp_record_complete,
  input logic [15:0] resp_record_ctrl_result,
  input logic [3:0] resp_record_freshness,
  input logic [31:0] resp_record_seq,
  input logic [3:0] resp_record_status,
  input logic resp_record_valid,
  input logic rst_n,
  input logic [127:0] s_axis_req_data,
  input logic s_axis_req_ready,
  input logic s_axis_req_valid
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(rst_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $error("Reset signal has X/Z state.");
  property p_s_axis_req_ready_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(s_axis_req_ready);
  endproperty

  a_s_axis_req_ready_known_after_reset: assert property(p_s_axis_req_ready_known_after_reset)
    else $error("Signal s_axis_req_ready has X/Z after reset release.");
  property p_m_axis_resp_data_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(m_axis_resp_data);
  endproperty

  a_m_axis_resp_data_known_after_reset: assert property(p_m_axis_resp_data_known_after_reset)
    else $error("Signal m_axis_resp_data has X/Z after reset release.");
  property p_m_axis_resp_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(m_axis_resp_valid);
  endproperty

  a_m_axis_resp_valid_known_after_reset: assert property(p_m_axis_resp_valid_known_after_reset)
    else $error("Signal m_axis_resp_valid has X/Z after reset release.");
  property p_m_axis_act_data_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(m_axis_act_data);
  endproperty

  a_m_axis_act_data_known_after_reset: assert property(p_m_axis_act_data_known_after_reset)
    else $error("Signal m_axis_act_data has X/Z after reset release.");
  property p_m_axis_act_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(m_axis_act_valid);
  endproperty

  a_m_axis_act_valid_known_after_reset: assert property(p_m_axis_act_valid_known_after_reset)
    else $error("Signal m_axis_act_valid has X/Z after reset release.");
  property p_csr_rd_data_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(csr_rd_data);
  endproperty

  a_csr_rd_data_known_after_reset: assert property(p_csr_rd_data_known_after_reset)
    else $error("Signal csr_rd_data has X/Z after reset release.");
  property p_csr_rd_valid_known_after_reset;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(csr_rd_valid);
  endproperty

  a_csr_rd_valid_known_after_reset: assert property(p_csr_rd_valid_known_after_reset)
    else $error("Signal csr_rd_valid has X/Z after reset release.");

endmodule
