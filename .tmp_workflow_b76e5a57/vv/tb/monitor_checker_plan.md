# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`
- Clock observations: `clk`
- Reset observations: `rst_n`

## Monitors
- Clock/reset monitor: observes reset assertion/deassertion and first active clock edges.
- Input stimulus monitor: records driven values on declared non-clock/reset inputs.
- Output response monitor: samples declared outputs after reset release and after stimulus changes.
- Coverage monitor: calls `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `mem_dout`
- `geometry_ref_in`
- `geometry_valid_in`

## Observed Outputs
- `mem_csb`
- `mem_we`
- `mem_addr`
- `mem_din`
- `geometry_ready_out`
- `geometry_summary_out`

## Checkers
- Reset known-value checker: outputs must not remain unknown after reset release and settle.
- Width/value checker: sampled signals are interpreted using spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: `Scoreboard` is loaded when `scoreboard.py` is present and can compare expected versus observed transactions.
- SVA hook: generated SVA/bind files are included through `verification_sources.mk` when available.

## Coverage Coupling
- Functional output points: `mem_csb`, `mem_we`, `mem_addr`, `mem_din`, `geometry_ready_out`, `geometry_summary_out`
- Functional input points: `clk`, `rst_n`, `mem_dout`, `geometry_ref_in`, `geometry_valid_in`

## Review Checklist
- Confirm each important requirement has a monitor point.
- Confirm each monitor feeds a checker, scoreboard, assertion, or coverage point.
- Add directed tests or custom scoreboard logic for behavior that cannot be inferred from ports alone.
