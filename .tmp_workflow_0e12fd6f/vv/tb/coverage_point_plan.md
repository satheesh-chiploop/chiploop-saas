# Coverage Point Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`

## Output Coverpoints
- Cover `s_axis_req_ready` zero and non-zero/value-transition bins.
- Cover `m_axis_resp_data` zero and non-zero/value-transition bins.
- Cover `m_axis_resp_valid` zero and non-zero/value-transition bins.
- Cover `m_axis_act_data` zero and non-zero/value-transition bins.
- Cover `m_axis_act_valid` zero and non-zero/value-transition bins.
- Cover `csr_rd_data` zero and non-zero/value-transition bins.
- Cover `csr_rd_valid` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `rst_n` zero and non-zero/input-stimulus bins.
- Cover `s_axis_req_data` zero and non-zero/input-stimulus bins.
- Cover `s_axis_req_valid` zero and non-zero/input-stimulus bins.
- Cover `m_axis_resp_ready` zero and non-zero/input-stimulus bins.
- Cover `m_axis_act_ready` zero and non-zero/input-stimulus bins.
- Cover `csr_addr_data` zero and non-zero/input-stimulus bins.
- Cover `csr_wr_en` zero and non-zero/input-stimulus bins.
- Cover `csr_wr_data` zero and non-zero/input-stimulus bins.
- Cover `mem_dout` zero and non-zero/input-stimulus bins.
- Cover `model_req_ready` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_valid` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_data` zero and non-zero/input-stimulus bins.
- Cover `resp_record_seq` zero and non-zero/input-stimulus bins.
- Cover `resp_record_status` zero and non-zero/input-stimulus bins.
- Cover `resp_record_freshness` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Add directed tests for missed bins.
- Waive bins only with reviewer rationale.
