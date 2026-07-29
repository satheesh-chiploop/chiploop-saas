# Synthesis Readiness Report

- Top: `pwm_fpga_demo`
- RTL files: `1`
- Score (heuristic): **44/100**

## Timing/Area Intent Checks
- (info) No clocks found in spec. If synchronous, include clock intent (name + freq/period).
- (info) No performance/timing intent section found (latency/throughput/constraints).
- (info) No area/gatecount intent found. Provide rough bounds if needed.

## Synthesizable Subset Red Flags
Found **1** potential issues (showing up to 30):

- `backend/workflows/df5cb77c-2018-4f04-abd8-78a7002cbac6/rtl/pwm_fpga_demo.v:48` — Use of initial blocks may be non-synthesizable (ASIC) or tool-dependent (FPGA).  
  `...initial begin...`

## Yosys Synthesis Check
- Return code: `1`
### Errors (first 20)
- ERROR: Can't open input file `backend/workflows/df5cb77c-2018-4f04-abd8-78a7002cbac6/rtl/pwm_fpga_demo.v' for reading: No such file or directory
