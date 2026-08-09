# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`
- Clock observations: `clk`
- Reset observations: `reset_n`

## Monitors
- Clock/reset monitor: observes reset assertion/deassertion and first active clock edges.
- Input stimulus monitor: records driven values on declared non-clock/reset inputs.
- Output response monitor: samples declared outputs after reset release and after stimulus changes.
- Coverage monitor: calls `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `reg_addr`
- `reg_wdata`
- `_we`
- `_re`
- `model_req_ready`
- `model_rsp_valid`
- `model_rsp_data`

## Observed Outputs
- `reg_rdata`
- `_ready`
- `model_req_valid`
- `model_req_data`
- `model_rsp_ready`
- `actuator_cmd`
- `safe_state`

## Checkers
- Reset known-value checker: outputs must not remain unknown after reset release and settle.
- Width/value checker: sampled signals are interpreted using spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: `Scoreboard` is loaded when `scoreboard.py` is present and can compare expected versus observed transactions.
- SVA hook: generated SVA/bind files are included through `verification_sources.mk` when available.

## Coverage Coupling
- Functional output points: `reg_rdata`, `_ready`, `model_req_valid`, `model_req_data`, `model_rsp_ready`, `actuator_cmd`, `safe_state`
- Functional input points: `clk`, `reset_n`, `reg_addr`, `reg_wdata`, `_we`, `_re`, `model_req_ready`, `model_rsp_valid`, `model_rsp_data`

## Review Checklist
- Confirm each important requirement has a monitor point.
- Confirm each monitor feeds a checker, scoreboard, assertion, or coverage point.
- Add directed tests or custom scoreboard logic for behavior that cannot be inferred from ports alone.
