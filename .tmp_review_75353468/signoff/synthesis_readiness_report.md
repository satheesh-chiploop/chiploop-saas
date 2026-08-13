# Synthesis Readiness Report

- Top: `sram_mbist_demo_controller`
- RTL files: `3`
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
- ERROR: Module `\sky130_sram_1kbyte_1rw1r_32x256_8' referenced in module `\demo_sram_32x256_wrapper' in cell `\u_sram' is not part of the design.
