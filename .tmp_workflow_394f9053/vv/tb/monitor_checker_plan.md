# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `pwm_controller`
- Clock observations: `clk`
- Reset observations: `reset_n`

## Monitors
- Clock/reset monitor: observe reset sequencing and active simulation edges.
- Input stimulus monitor: record values driven on declared inputs.
- Output response monitor: sample declared outputs after reset and stimulus changes.
- Coverage monitor: call `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `clk`
- `reset_n`
- `enable`
- `duty_cycle`
- `period`

## Observed Outputs
- `pwm_out`
- `counter_value`

## Checkers
- Reset known-value checker: outputs should settle after reset release.
- Width/value checker: sampled signals use spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: compare expected versus observed transactions when `scoreboard.py` is present.
- SVA hook: include generated assertion bind files when available.

## Coverage Coupling
- Functional output points: `pwm_out`, `counter_value`
- Functional input points: `clk`, `reset_n`, `enable`, `duty_cycle`, `period`

## Review Checklist
- Every important requirement should have a monitor point.
- Every monitor should feed a checker, scoreboard, assertion, or coverage point.
- Add custom scoreboard logic for behavior that cannot be inferred from ports alone.
