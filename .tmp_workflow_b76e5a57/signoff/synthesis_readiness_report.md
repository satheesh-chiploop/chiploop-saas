# Synthesis Readiness Report

- Top: `adaptive_aero_control_top`
- RTL files: `5`
- Score (heuristic): **45/100**

## Timing/Area Intent Checks
- (info) No clocks found in spec. If synchronous, include clock intent (name + freq/period).
- (info) No performance/timing intent section found (latency/throughput/constraints).
- (info) No area/gatecount intent found. Provide rough bounds if needed.

## Synthesizable Subset Red Flags
No obvious red flags found by regex scan.

## Yosys Synthesis Check
- Return code: `1`
### Errors (first 20)
- ERROR: Can't open input file `backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v' for reading: No such file or directory
