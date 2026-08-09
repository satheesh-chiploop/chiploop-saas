# Synthesis Readiness Report

- Top: `adaptive_aero_control_top`
- RTL files: `4`
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
- /root/chiploop-backend/backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/adaptive_aero_control_top.v:1: ERROR: Re-definition of module `\adaptive_aero_control_top'!
