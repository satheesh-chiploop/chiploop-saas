# Coverage Point Plan

- Source: generated_from_spec
- Top module: `domino_active_aero_control_wrapper`

## Output Coverpoints
- Cover `host_cfg_ready` zero and non-zero/value-transition bins.
- Cover `host_cfg_rdata` zero and non-zero/value-transition bins.
- Cover `host_cfg_rvalid` zero and non-zero/value-transition bins.
- Cover `model_req_valid` zero and non-zero/value-transition bins.
- Cover `model_req_id` zero and non-zero/value-transition bins.
- Cover `model_req_epoch` zero and non-zero/value-transition bins.
- Cover `model_req_geometry_handle` zero and non-zero/value-transition bins.
- Cover `model_req_stream_velocity_mps` zero and non-zero/value-transition bins.
- Cover `model_req_timeout_cycles` zero and non-zero/value-transition bins.
- Cover `actuator_cmd_valid` zero and non-zero/value-transition bins.
- Cover `actuator_cmd` zero and non-zero/value-transition bins.
- Cover `actuator_cmd_safe_fallback` zero and non-zero/value-transition bins.
- Cover `cmd_clamped` zero and non-zero/value-transition bins.
- Cover `status_mode_fallback` zero and non-zero/value-transition bins.
- Cover `status_mode_model` zero and non-zero/value-transition bins.
- Cover `status_stale_rejected` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `rst_n` zero and non-zero/input-stimulus bins.
- Cover `host_cfg_valid` zero and non-zero/input-stimulus bins.
- Cover `host_cfg_write` zero and non-zero/input-stimulus bins.
- Cover `host_cfg_addr` zero and non-zero/input-stimulus bins.
- Cover `host_cfg_wdata` zero and non-zero/input-stimulus bins.
- Cover `enable` zero and non-zero/input-stimulus bins.
- Cover `freshness_timeout_cycles` zero and non-zero/input-stimulus bins.
- Cover `request_timeout_cycles` zero and non-zero/input-stimulus bins.
- Cover `actuator_min_limit` zero and non-zero/input-stimulus bins.
- Cover `actuator_max_limit` zero and non-zero/input-stimulus bins.
- Cover `safe_fallback_command_value` zero and non-zero/input-stimulus bins.
- Cover `stream_velocity_mps` zero and non-zero/input-stimulus bins.
- Cover `flow_update_strobe` zero and non-zero/input-stimulus bins.
- Cover `geometry_update_strobe` zero and non-zero/input-stimulus bins.
- Cover `geometry_format_selector` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
