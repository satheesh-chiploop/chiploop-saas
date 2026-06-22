<!-- ASSUMPTION: Replace placeholders with concrete file paths before execution. -->
<!-- ASSUMPTION: Cocotb integration is driven externally through pytest/cocotb makefile flow. -->

# Verilator Build Plan

## Inputs
- RTL top module: pwm_controller
- RTL filelist: /root/chiploop-backend/backend/workflows/8778ea73-6136-4e5a-873d-f91f99b0be67/firmware/validate/verilator_rtl_filelist.f
- Optional include flags: <OPTIONAL_INCLUDE_FLAGS>
- Optional define flags: <OPTIONAL_DEFINE_FLAGS>
- Cocotb Python test/harness: firmware/validate/cocotb_harness.py

## Deterministic command template

verilator -cc --build --trace --top-module pwm_controller \
  -f /root/chiploop-backend/backend/workflows/8778ea73-6136-4e5a-873d-f91f99b0be67/firmware/validate/verilator_rtl_filelist.f \
  <OPTIONAL_INCLUDE_FLAGS> \
  <OPTIONAL_DEFINE_FLAGS> \
  

## Expected outputs
- Build directory: obj_dir/
- Generated make/build products under: obj_dir/
- Runnable binary name: obj_dir/Vpwm_controller

## Notes
- Python cocotb tests are executed via pytest or cocotb makefile flow.
- Do not pass Python files to --exe.
- If firmware/ELF integration is needed, handle it via simulator memory preload or cocotb hooks.
