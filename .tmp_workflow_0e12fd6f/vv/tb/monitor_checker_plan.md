# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`
- Clock observations: `clk`
- Reset observations: `rst_n`

## Monitors
- Clock/reset monitor: observe reset sequencing and active simulation edges.
- Input stimulus monitor: record values driven on declared inputs.
- Output response monitor: sample declared outputs after reset and stimulus changes.
- Coverage monitor: call `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `clk`
- `rst_n`
- `s_axis_req_data`
- `s_axis_req_valid`
- `m_axis_resp_ready`
- `m_axis_act_ready`
- `csr_addr_data`
- `csr_wr_en`
- `csr_wr_data`
- `mem_dout`
- `model_req_ready`
- `model_rsp_valid`
- `model_rsp_data`
- `resp_record_seq`
- `resp_record_status`
- `resp_record_freshness`

## Observed Outputs
- `s_axis_req_ready`
- `m_axis_resp_data`
- `m_axis_resp_valid`
- `m_axis_act_data`
- `m_axis_act_valid`
- `csr_rd_data`
- `csr_rd_valid`

## Checkers
- Reset known-value checker: outputs should settle after reset release.
- Width/value checker: sampled signals use spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: compare expected versus observed transactions when `scoreboard.py` is present.
- SVA hook: include generated assertion bind files when available.

## Coverage Coupling
- Functional output points: `s_axis_req_ready`, `m_axis_resp_data`, `m_axis_resp_valid`, `m_axis_act_data`, `m_axis_act_valid`, `csr_rd_data`, `csr_rd_valid`
- Functional input points: `clk`, `rst_n`, `s_axis_req_data`, `s_axis_req_valid`, `m_axis_resp_ready`, `m_axis_act_ready`, `csr_addr_data`, `csr_wr_en`, `csr_wr_data`, `mem_dout`, `model_req_ready`, `model_rsp_valid`, `model_rsp_data`, `resp_record_seq`, `resp_record_status`, `resp_record_freshness`

## Review Checklist
- Every important requirement should have a monitor point.
- Every monitor should feed a checker, scoreboard, assertion, or coverage point.
- Add custom scoreboard logic for behavior that cannot be inferred from ports alone.
