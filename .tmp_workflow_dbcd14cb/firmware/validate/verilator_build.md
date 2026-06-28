<!-- ASSUMPTION: Replace placeholders with concrete file paths before execution. -->
<!-- ASSUMPTION: Cocotb integration is driven externally through pytest/cocotb makefile flow. -->

# Verilator Build Plan

## Inputs
- RTL top module: temp_monitor_soc_sim
- RTL filelist: artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dbcd14cb-c206-4b70-b2cc-5eeed0d92698/b59df0e7-5965-4c86-be8c-aa5cf85abd3f/digital/system/integration/system_rtl_filelist_sim.txt
- Optional include flags: <OPTIONAL_INCLUDE_FLAGS>
- Optional define flags: <OPTIONAL_DEFINE_FLAGS>
- Cocotb Python test/harness: firmware/validate/cocotb_harness.py

## Deterministic command template

verilator -cc --build --trace --top-module temp_monitor_soc_sim \
  -f artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dbcd14cb-c206-4b70-b2cc-5eeed0d92698/b59df0e7-5965-4c86-be8c-aa5cf85abd3f/digital/system/integration/system_rtl_filelist_sim.txt \
  <OPTIONAL_INCLUDE_FLAGS> \
  <OPTIONAL_DEFINE_FLAGS> \
  

## Expected outputs
- Build directory: obj_dir/
- Generated make/build products under: obj_dir/
- Runnable binary name: obj_dir/Vtemp_monitor_soc_sim

## Notes
- Python cocotb tests are executed via pytest or cocotb makefile flow.
- Do not pass Python files to --exe.
- If firmware/ELF integration is needed, handle it via simulator memory preload or cocotb hooks.
