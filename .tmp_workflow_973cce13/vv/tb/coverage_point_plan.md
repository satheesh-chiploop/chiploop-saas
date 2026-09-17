# Coverage Point Plan

- Source: generated_from_spec
- Top module: `pwm_controller`

## Output Coverpoints
- Cover `pwm_out` zero and non-zero/value-transition bins.
- Cover `counter_value` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `reset_n` zero and non-zero/input-stimulus bins.
- Cover `enable` zero and non-zero/input-stimulus bins.
- Cover `duty_cycle` zero and non-zero/input-stimulus bins.
- Cover `period` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Add directed tests for missed bins.
- Waive bins only with reviewer rationale.
