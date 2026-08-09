# Coverage Point Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`

## Output Coverpoints
- Cover `reg_rdata` zero and non-zero/value-transition bins.
- Cover `_ready` zero and non-zero/value-transition bins.
- Cover `model_req_valid` zero and non-zero/value-transition bins.
- Cover `model_req_data` zero and non-zero/value-transition bins.
- Cover `model_rsp_ready` zero and non-zero/value-transition bins.
- Cover `actuator_cmd` zero and non-zero/value-transition bins.
- Cover `safe_state` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `reset_n` zero and non-zero/input-stimulus bins.
- Cover `reg_addr` zero and non-zero/input-stimulus bins.
- Cover `reg_wdata` zero and non-zero/input-stimulus bins.
- Cover `_we` zero and non-zero/input-stimulus bins.
- Cover `_re` zero and non-zero/input-stimulus bins.
- Cover `model_req_ready` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_valid` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_data` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
