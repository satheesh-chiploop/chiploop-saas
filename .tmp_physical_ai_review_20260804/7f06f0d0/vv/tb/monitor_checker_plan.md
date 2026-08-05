# Monitor And Checker Plan

- Source: generated_from_spec
- Top module: `aero_safety_controller`
- Clock observations: `clk`
- Reset observations: `rst_n`

## Monitors
- Clock/reset monitor: observes reset assertion/deassertion and first active clock edges.
- Input stimulus monitor: records driven values on declared non-clock/reset inputs.
- Output response monitor: samples declared outputs after reset release and after stimulus changes.
- Coverage monitor: calls `CoverageModel.sample()` at transaction/checkpoint boundaries.

## Observed Inputs
- `tick_1ms`
- `host_reg_wr_valid`
- `host_reg_rd_valid`
- `host_reg_addr`
- `host_reg_wdata`
- `stream_velocity_mps`
- `geom_valid`
- `geom_format_id_in`
- `geom_source_id_in`
- `geom_version_in`
- `model_req_ready`
- `model_rsp_valid`
- `model_rsp_seq`
- `model_rsp_drag_force`
- `model_rsp_lift_force`
- `model_rsp_surface_pressure`

## Observed Outputs
- `host_reg_ready`
- `host_reg_rdata`
- `host_reg_rvalid`
- `model_req_valid`
- `model_req_seq`
- `model_req_enable`
- `model_req_stream_velocity_mps`
- `model_req_velocity_min_limit`
- `model_req_velocity_max_limit`
- `model_req_actuator_min_limit`
- `model_req_actuator_max_limit`
- `model_req_actuator_safe_position`
- `model_req_command_timeout_cycles`
- `model_req_max_slew_rate`
- `model_req_geometry_format_id`
- `model_req_geometry_source_id`

## Checkers
- Reset known-value checker: outputs must not remain unknown after reset release and settle.
- Width/value checker: sampled signals are interpreted using spec-declared widths.
- Scenario checker: directed tests should encode expected responses from the verification plan.
- Scoreboard hook: `Scoreboard` is loaded when `scoreboard.py` is present and can compare expected versus observed transactions.
- SVA hook: generated SVA/bind files are included through `verification_sources.mk` when available.

## Coverage Coupling
- Functional output points: `host_reg_ready`, `host_reg_rdata`, `host_reg_rvalid`, `model_req_valid`, `model_req_seq`, `model_req_enable`, `model_req_stream_velocity_mps`, `model_req_velocity_min_limit`, `model_req_velocity_max_limit`, `model_req_actuator_min_limit`, `model_req_actuator_max_limit`, `model_req_actuator_safe_position`, `model_req_command_timeout_cycles`, `model_req_max_slew_rate`, `model_req_geometry_format_id`, `model_req_geometry_source_id`
- Functional input points: `clk`, `rst_n`, `tick_1ms`, `host_reg_wr_valid`, `host_reg_rd_valid`, `host_reg_addr`, `host_reg_wdata`, `stream_velocity_mps`, `geom_valid`, `geom_format_id_in`, `geom_source_id_in`, `geom_version_in`, `model_req_ready`, `model_rsp_valid`, `model_rsp_seq`, `model_rsp_drag_force`

## Review Checklist
- Confirm each important requirement has a monitor point.
- Confirm each monitor feeds a checker, scoreboard, assertion, or coverage point.
- Add directed tests or custom scoreboard logic for behavior that cannot be inferred from ports alone.
