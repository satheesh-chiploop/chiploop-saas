# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `pwm_controller`
- Clock observations: `clk`
- Reset observations: `reset_n`

## Monitors
- Clock/reset monitor: observes reset assertion/deassertion and first active clock edges.
- Input stimulus monitor: records driven values on declared non-clock/reset inputs.
- Output response monitor: samples declared outputs after reset release and after stimulus changes.
- Coverage monitor: calls `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `wr_en`
- `wr_addr`
- `wr_data`
- `rd_en`
- `rd_addr`

## Observed Outputs
- `rd_data`
- `pwm_out`
- `counter_value`

## Checkers
- Reset known-value checker: outputs must not remain unknown after reset release and settle.
- Width/value checker: sampled signals are interpreted using spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: `Scoreboard` is loaded when `scoreboard.py` is present and can compare expected versus observed transactions.
- SVA hook: generated SVA/bind files are included through `verification_sources.mk` when available.

## Coverage Coupling
- Functional output points: `rd_data`, `pwm_out`, `counter_value`
- Functional input points: `clk`, `reset_n`, `wr_en`, `wr_addr`, `wr_data`, `rd_en`, `rd_addr`

## Review Checklist
- Confirm each important requirement has a monitor point.
- Confirm each monitor feeds a checker, scoreboard, assertion, or coverage point.
- Add directed tests or custom scoreboard logic for behavior that cannot be inferred from ports alone.
