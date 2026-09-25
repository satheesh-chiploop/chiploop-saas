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

## Feature Coverage
- `reset_clears_state`: reset_clears_state.stimulus_applied, reset_clears_state.expected_observed (executable)
- `increment_while_enabled`: increment_while_enabled.stimulus_applied, increment_while_enabled.expected_observed (executable)
- `wrap_on_period`: wrap_on_period.stimulus_applied, wrap_on_period.expected_observed (executable)
- `pwm_compare_reflects_duty`: pwm_compare_reflects_duty.stimulus_applied, pwm_compare_reflects_duty.expected_observed (executable)

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
