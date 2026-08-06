# Functional Coverage Summary

- Top module: domino_active_aero_control_wrapper
- Functional coverage: 70.31%
- Bins hit: 45
- Total bins: 64

## Outputs
- host_cfg_ready: samples=25, bins=2/2
- host_cfg_rdata: samples=25, bins=1/2
- host_cfg_rvalid: samples=25, bins=2/2
- model_req_valid: samples=25, bins=1/2
- model_req_id: samples=25, bins=1/2
- model_req_epoch: samples=25, bins=1/2
- model_req_geometry_handle: samples=25, bins=1/2
- model_req_stream_velocity_mps: samples=25, bins=1/2
- model_req_timeout_cycles: samples=25, bins=2/2
- actuator_cmd_valid: samples=25, bins=2/2
- actuator_cmd: samples=25, bins=2/2
- actuator_cmd_safe_fallback: samples=25, bins=1/2
- cmd_clamped: samples=25, bins=2/2
- status_mode_fallback: samples=25, bins=1/2
- status_mode_model: samples=25, bins=1/2
- status_stale_rejected: samples=25, bins=2/2

## Inputs
- clk: samples=25, bins=1/2
- rst_n: samples=25, bins=1/2
- host_cfg_valid: samples=25, bins=2/2
- host_cfg_write: samples=25, bins=2/2
- host_cfg_addr: samples=25, bins=1/2
- host_cfg_wdata: samples=25, bins=1/2
- enable: samples=25, bins=2/2
- freshness_timeout_cycles: samples=25, bins=1/2
- request_timeout_cycles: samples=25, bins=1/2
- actuator_min_limit: samples=25, bins=1/2
- actuator_max_limit: samples=25, bins=1/2
- safe_fallback_command_value: samples=25, bins=1/2
- stream_velocity_mps: samples=25, bins=1/2
- flow_update_strobe: samples=25, bins=2/2
- geometry_update_strobe: samples=25, bins=2/2
- geometry_format_selector: samples=25, bins=2/2
