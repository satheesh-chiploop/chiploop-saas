# Coverage Point Plan

- Source: generated_from_spec
- Top module: `adaptive_aero_control_top_spi_fpga_top`

## Output Coverpoints
- Cover `spi_miso` zero and non-zero/value-transition bins.
- Cover `fault_indicator` zero and non-zero/value-transition bins.

## Input Coverpoints
- Cover `clk` zero and non-zero/input-stimulus bins.
- Cover `reset_n` zero and non-zero/input-stimulus bins.
- Cover `spi_sclk` zero and non-zero/input-stimulus bins.
- Cover `spi_cs_n` zero and non-zero/input-stimulus bins.
- Cover `spi_mosi` zero and non-zero/input-stimulus bins.

## Cross Coverage Candidates
- Cross reset release with first observed output activity.
- Cross primary control inputs with output response bins when both are present.

## Closure Guidance
- Review uncovered bins before accepting closure.
- Add directed tests for missed bins, or mark exclusions with reviewer rationale.
