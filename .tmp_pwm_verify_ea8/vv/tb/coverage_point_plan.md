# Coverage Point Plan

- Source: generated_from_spec
- Top module: `pwm_controller`

## Output Coverpoints
- Cover `rd_data` zero and non-zero/value-transition bins.
- Cover `pwm_out` zero and non-zero/value-transition bins.
- Cover `counter_value` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `reset_n` zero and non-zero/input-stimulus bins.
- Cover `wr_en` zero and non-zero/input-stimulus bins.
- Cover `wr_addr` zero and non-zero/input-stimulus bins.
- Cover `wr_data` zero and non-zero/input-stimulus bins.
- Cover `rd_en` zero and non-zero/input-stimulus bins.
- Cover `rd_addr` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
