# Coverage Point Plan

- Source: generated_from_spec
- Top module: `pwm_fpga_demo`

## Output Coverpoints
- Cover `led` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
