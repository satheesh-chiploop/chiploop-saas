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
- `count_increments_when_enabled`: count_increments_when_enabled.stimulus_applied, count_increments_when_enabled.expected_observed (executable)
- `counter_wraps_at_period`: counter_wraps_at_period.stimulus_applied, counter_wraps_at_period.expected_observed (executable)
- `pwm_output_follows_comparison`: pwm_output_follows_comparison.stimulus_applied, pwm_output_follows_comparison.expected_observed (executable)
- `hold_when_disabled`: hold_when_disabled.stimulus_applied, hold_when_disabled.expected_observed (executable)

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
