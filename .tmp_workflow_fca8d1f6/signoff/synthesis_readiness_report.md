# Synthesis Readiness Report

- Top: `adaptive_aero_control_top_spi_fpga_top`
- RTL files: `5`
- Score (heuristic): **84/100**

## Timing/Area Intent Checks
- (info) No clocks found in spec. If synchronous, include clock intent (name + freq/period).
- (info) No performance/timing intent section found (latency/throughput/constraints).
- (info) No area/gatecount intent found. Provide rough bounds if needed.

## Synthesizable Subset Red Flags
Found **1** potential issues (showing up to 30):

- `backend/workflows/fca8d1f6-5127-4f67-ac36-c90825d4284d/fpga/src/upstream/adaptive_aero_control_top.v:177` — Use of initial blocks may be non-synthesizable (ASIC) or tool-dependent (FPGA).  
  `...initial begin...`

## Yosys Synthesis Check
- Return code: `0`
- No Yosys ERROR lines detected.

### Warnings (first 20)
- Warning: Yosys has only limited support for tri-state logic at the moment. (/root/chiploop-backend/backend/workflows/fca8d1f6-5127-4f67-ac36-c90825d4284d/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv:80)
