# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `domino_active_aero_control_wrapper`
- Clock observations: `clk`
- Reset observations: `rst_n`

## Monitors
- Clock/reset monitor: observes reset assertion/deassertion and first active clock edges.
- Input stimulus monitor: records driven values on declared non-clock/reset inputs.
- Output response monitor: samples declared outputs after reset release and after stimulus changes.
- Coverage monitor: calls `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `host_cfg_valid`
- `host_cfg_write`
- `host_cfg_addr`
- `host_cfg_wdata`
- `enable`
- `freshness_timeout_cycles`
- `request_timeout_cycles`
- `actuator_min_limit`
- `actuator_max_limit`
- `safe_fallback_command_value`
- `stream_velocity_mps`
- `flow_update_strobe`
- `geometry_update_strobe`
- `geometry_format_selector`
- `geometry_metadata_valid`
- `geometry_metadata_tag`

## Observed Outputs
- `host_cfg_ready`
- `host_cfg_rdata`
- `host_cfg_rvalid`
- `model_req_valid`
- `model_req_id`
- `model_req_epoch`
- `model_req_geometry_handle`
- `model_req_stream_velocity_mps`
- `model_req_timeout_cycles`
- `actuator_cmd_valid`
- `actuator_cmd`
- `actuator_cmd_safe_fallback`
- `cmd_clamped`
- `status_mode_fallback`
- `status_mode_model`
- `status_stale_rejected`

## Checkers
- Reset known-value checker: outputs must not remain unknown after reset release and settle.
- Width/value checker: sampled signals are interpreted using spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: `Scoreboard` is loaded when `scoreboard.py` is present and can compare expected versus observed transactions.
- SVA hook: generated SVA/bind files are included through `verification_sources.mk` when available.

## Coverage Coupling
- Functional output points: `host_cfg_ready`, `host_cfg_rdata`, `host_cfg_rvalid`, `model_req_valid`, `model_req_id`, `model_req_epoch`, `model_req_geometry_handle`, `model_req_stream_velocity_mps`, `model_req_timeout_cycles`, `actuator_cmd_valid`, `actuator_cmd`, `actuator_cmd_safe_fallback`, `cmd_clamped`, `status_mode_fallback`, `status_mode_model`, `status_stale_rejected`
- Functional input points: `clk`, `rst_n`, `host_cfg_valid`, `host_cfg_write`, `host_cfg_addr`, `host_cfg_wdata`, `enable`, `freshness_timeout_cycles`, `request_timeout_cycles`, `actuator_min_limit`, `actuator_max_limit`, `safe_fallback_command_value`, `stream_velocity_mps`, `flow_update_strobe`, `geometry_update_strobe`, `geometry_format_selector`

## Review Checklist
- Confirm each important requirement has a monitor point.
- Confirm each monitor feeds a checker, scoreboard, assertion, or coverage point.
- Add directed tests or custom scoreboard logic for behavior that cannot be inferred from ports alone.
