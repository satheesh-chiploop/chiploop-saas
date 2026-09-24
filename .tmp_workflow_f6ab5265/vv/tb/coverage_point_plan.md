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
- `counting_advances_when_enabled`: counting_advances_when_enabled.stimulus_applied, counting_advances_when_enabled.expected_observed (executable)
- `counter_holds_when_disabled`: counter_holds_when_disabled.stimulus_applied, counter_holds_when_disabled.expected_observed (executable)
- `pwm_deasserts_at_or_above_duty`: pwm_deasserts_at_or_above_duty.stimulus_applied, pwm_deasserts_at_or_above_duty.expected_observed (executable)
- `rollover_on_period`: rollover_on_period.stimulus_applied, rollover_on_period.expected_observed (executable)

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
