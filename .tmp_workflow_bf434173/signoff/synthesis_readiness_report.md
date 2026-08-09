# Synthesis Readiness Report

- Top: `pwm_fpga_demo`
- RTL files: `1`
- Score (heuristic): **84/100**

## Timing/Area Intent Checks
- (info) No clocks found in spec. If synchronous, include clock intent (name + freq/period).
- (info) No performance/timing intent section found (latency/throughput/constraints).
- (info) No area/gatecount intent found. Provide rough bounds if needed.

## Synthesizable Subset Red Flags
Found **1** potential issues (showing up to 30):

- `backend/workflows/bf434173-b47d-4407-865d-8a369997c048/rtl/pwm_fpga_demo.v:42` — Use of initial blocks may be non-synthesizable (ASIC) or tool-dependent (FPGA).  
  `...initial begin...`

## Yosys Synthesis Check
- Return code: `0`
- No Yosys ERROR lines detected.
