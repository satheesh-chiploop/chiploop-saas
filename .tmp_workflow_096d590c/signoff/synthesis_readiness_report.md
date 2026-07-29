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

- `backend/workflows/096d590c-4522-4512-9780-c543ada0da2a/rtl/pwm_fpga_demo.v:40` — Use of initial blocks may be non-synthesizable (ASIC) or tool-dependent (FPGA).  
  `...initial begin...`

## Yosys Synthesis Check
- Return code: `1`
### Errors (first 20)
- ERROR: Can't open input file `backend/workflows/096d590c-4522-4512-9780-c543ada0da2a/rtl/pwm_fpga_demo.v' for reading: No such file or directory
