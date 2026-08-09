# Coverage Point Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top`

## Output Coverpoints
- Cover `mem_csb` zero and non-zero/value-transition bins.
- Cover `mem_we` zero and non-zero/value-transition bins.
- Cover `mem_addr` zero and non-zero/value-transition bins.
- Cover `mem_din` zero and non-zero/value-transition bins.
- Cover `geometry_ready_out` zero and non-zero/value-transition bins.
- Cover `geometry_summary_out` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `rst_n` zero and non-zero/input-stimulus bins.
- Cover `mem_dout` zero and non-zero/input-stimulus bins.
- Cover `geometry_ref_in` zero and non-zero/input-stimulus bins.
- Cover `geometry_valid_in` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
