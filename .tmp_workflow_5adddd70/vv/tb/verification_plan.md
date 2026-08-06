# Verification Plan

- Source: generated_from_spec
- Top module: `domino_active_aero_control_wrapper`
- Clocks: `clk`
- Resets: `rst_n`

## User/Test Intent
No explicit test intent was provided. The plan is derived from the resolved RTL specification.

## Interfaces Under Test
### Inputs
- `clk` width `1`
- `rst_n` width `1`
- `host_cfg_valid` width `1`
- `host_cfg_write` width `1`
- `host_cfg_addr` width `8`
- `host_cfg_wdata` width `32`
- `enable` width `1`
- `freshness_timeout_cycles` width `16`
- `request_timeout_cycles` width `16`
- `actuator_min_limit` width `16`
- `actuator_max_limit` width `16`
- `safe_fallback_command_value` width `16`
- `stream_velocity_mps` width `16`
- `flow_update_strobe` width `1`
- `geometry_update_strobe` width `1`
- `geometry_format_selector` width `8`
- `geometry_metadata_valid` width `1`
- `geometry_metadata_tag` width `16`
- `geometry_handle_in` width `32`
- `geometry_reference_is_driaverml_stl` width `1`
- `fault_clear` width `1`
- `mode_select_fallback_when_valid` width `1`
- `model_req_ready` width `1`
- `model_rsp_valid` width `1`
- `model_rsp_id` width `32`
- `model_rsp_epoch` width `32`
- `model_rsp_status_valid` width `1`
- `model_rsp_status_unavailable` width `1`
- `model_rsp_drag_force` width `32`
- `model_rsp_lift_force` width `32`
- `model_rsp_surface_pressure` width `32`
- `model_rsp_flow_field_meta` width `32`
- `telemetry_ready` width `1`

### Outputs
- `host_cfg_ready` width `1`
- `host_cfg_rdata` width `32`
- `host_cfg_rvalid` width `1`
- `model_req_valid` width `1`
- `model_req_id` width `32`
- `model_req_epoch` width `32`
- `model_req_geometry_handle` width `32`
- `model_req_stream_velocity_mps` width `16`
- `model_req_timeout_cycles` width `16`
- `actuator_cmd_valid` width `1`
- `actuator_cmd` width `16`
- `actuator_cmd_safe_fallback` width `1`
- `cmd_clamped` width `1`
- `status_mode_fallback` width `1`
- `status_mode_model` width `1`
- `status_stale_rejected` width `1`
- `status_faulted` width `1`
- `status_req_id` width `32`
- `status_rsp_id` width `32`
- `status_last_accepted_req_id` width `32`
- `status_last_accepted_rsp_id` width `32`
- `status_cfg_fault` width `1`
- `status_geometry_fault` width `1`
- `status_flow_fault` width `1`
- `status_request_timeout_fault` width `1`
- `status_stale_response_fault` width `1`
- `status_response_mismatch_fault` width `1`
- `status_model_unavailable_fault` width `1`
- `status_actuator_saturation_fault` width `1`
- `telemetry_valid` width `1`
- `telemetry_mode` width `2`
- `telemetry_fault_bits` width `8`
- `telemetry_stale` width `1`
- `telemetry_req_id` width `32`
- `telemetry_rsp_id` width `32`
- `telemetry_last_clamped` width `1`
- `telemetry_last_fallback` width `1`

## Planned Tests
- Reset/boot smoke test: drive reset, release reset, confirm stable known behavior.
- Register or control path test: exercise configuration/control inputs and observe outputs.
- Directed scenario tests: cover the key user intent and spec-declared behavior.
- Constrained-random sanity: vary input values around zero, one, max, and non-zero buckets.
- Output stability checks: confirm outputs do not become unknown after reset release.

## Assertions And Checks
- Reset sequencing checks for declared reset ports.
- Clocked output known-value checks after reset release.
- Interface-specific checks generated from port directions and widths.

## Closure Criteria
- All generated simulation tests pass.
- Functional coverage points in `coverage_point_plan.md` are reviewed and either hit or waived.
- Code coverage and formal results are reviewed when enabled for this run.
