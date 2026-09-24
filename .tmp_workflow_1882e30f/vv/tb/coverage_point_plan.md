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
- `reset_clears_outputs_and_counter`: reset_clears_outputs_and_counter.stimulus_applied, reset_clears_outputs_and_counter.expected_observed (executable)
- `enabled_counter_increments_from_zero`: enabled_counter_increments_from_zero.stimulus_applied, enabled_counter_increments_from_zero.expected_observed (executable)
- `counter_wraps_at_period`: counter_wraps_at_period.stimulus_applied, counter_wraps_at_period.expected_observed (executable)
- `disabled_counter_holds_value`: disabled_counter_holds_value.stimulus_applied, disabled_counter_holds_value.expected_observed (executable)

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
