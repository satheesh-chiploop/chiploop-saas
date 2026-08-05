# Coverage Point Plan

- Source: generated_from_spec
- Top module: `aero_safety_controller`

## Output Coverpoints
- Cover `host_reg_ready` zero and non-zero/value-transition bins.
- Cover `host_reg_rdata` zero and non-zero/value-transition bins.
- Cover `host_reg_rvalid` zero and non-zero/value-transition bins.
- Cover `model_req_valid` zero and non-zero/value-transition bins.
- Cover `model_req_seq` zero and non-zero/value-transition bins.
- Cover `model_req_enable` zero and non-zero/value-transition bins.
- Cover `model_req_stream_velocity_mps` zero and non-zero/value-transition bins.
- Cover `model_req_velocity_min_limit` zero and non-zero/value-transition bins.
- Cover `model_req_velocity_max_limit` zero and non-zero/value-transition bins.
- Cover `model_req_actuator_min_limit` zero and non-zero/value-transition bins.
- Cover `model_req_actuator_max_limit` zero and non-zero/value-transition bins.
- Cover `model_req_actuator_safe_position` zero and non-zero/value-transition bins.
- Cover `model_req_command_timeout_cycles` zero and non-zero/value-transition bins.
- Cover `model_req_max_slew_rate` zero and non-zero/value-transition bins.
- Cover `model_req_geometry_format_id` zero and non-zero/value-transition bins.
- Cover `model_req_geometry_source_id` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `rst_n` zero and non-zero/input-stimulus bins.
- Cover `tick_1ms` zero and non-zero/input-stimulus bins.
- Cover `host_reg_wr_valid` zero and non-zero/input-stimulus bins.
- Cover `host_reg_rd_valid` zero and non-zero/input-stimulus bins.
- Cover `host_reg_addr` zero and non-zero/input-stimulus bins.
- Cover `host_reg_wdata` zero and non-zero/input-stimulus bins.
- Cover `stream_velocity_mps` zero and non-zero/input-stimulus bins.
- Cover `geom_valid` zero and non-zero/input-stimulus bins.
- Cover `geom_format_id_in` zero and non-zero/input-stimulus bins.
- Cover `geom_source_id_in` zero and non-zero/input-stimulus bins.
- Cover `geom_version_in` zero and non-zero/input-stimulus bins.
- Cover `model_req_ready` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_valid` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_seq` zero and non-zero/input-stimulus bins.
- Cover `model_rsp_drag_force` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
