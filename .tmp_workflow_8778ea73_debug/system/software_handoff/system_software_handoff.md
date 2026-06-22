# System Software Handoff Package

- Generated at: 2026-06-22T19:07:42.402739+00:00
- Source workflow id: 8778ea73-6136-4e5a-873d-f91f99b0be67
- Package version: 2.0

## Overview

- Top module: `pwm_controller`
- SoC sim top path: `digital/rtl/demo_sram_32x256_model.v`
- RTL file count: `4`
- Firmware ELF path: `firmware/build/target/x86_64-unknown-linux-gnu/release/firmware_app.elf`
- Firmware ELF exists: `True`
- Firmware ELF placeholder: `False`
- System firmware execution readiness: `ready`
- Coverage available: `False`

## Artifacts

- `digital/rtl/demo_sram_32x256_model.v`
- `firmware/firmware_manifest.json`
- `firmware/register_map.json`
- `firmware/hal/registers.rs`
- `firmware/drivers/driver_scaffold.rs`
- `firmware/diagnostics/register_dump.rs`
- `firmware/isr/interrupt_map.json`
- `firmware/build/target/x86_64-unknown-linux-gnu/release/firmware_app.elf`
- `firmware/validate/Makefile`
- `firmware/validate/test_firmware_smoke.py`
- `firmware/validate/cocotb_harness.py`
- `firmware/validate/validation_report.md`
- `firmware/register_map_debug.json`
- `firmware/register_map_summary.json`
- `firmware/src/hal/mod.rs`
- `firmware/isr/interrupts.rs`
- `firmware/isr/interrupts_debug.json`
- `firmware/isr/interrupts_summary.json`
- `firmware/handoff/digital_handoff_ingest.json`
- `firmware/hal/register_validation.json`
- `firmware/hal/register_validation.md`
- `firmware/hal/register_validation_debug.json`
- `firmware/hal/registers_debug.json`
- `firmware/hal/registers_summary.json`
- `firmware/drivers/driver_scaffold_debug.json`
- `firmware/drivers/driver_scaffold_summary.json`

## Required inputs for System_Software

- `register_map_path` → `firmware/register_map.json`
- `hal_path` → `firmware/hal/registers.rs`
- `driver_path` → `firmware/drivers/driver_scaffold.rs`
- `firmware_manifest_path` → `firmware/firmware_manifest.json`
- `system_integration_intent_path` → `missing`

## Recommended inputs for System_Software

- `register_dump_path` → `firmware/diagnostics/register_dump.rs`
- `interrupt_mapping_path` → `firmware/isr/interrupt_map.json`
- `dma_integration_path` → `unavailable`
- `boot_dependency_plan_path` → `unavailable`
- `clock_config_path` → `unavailable`
- `reset_sequence_path` → `unavailable`
- `power_mode_path` → `unavailable`
- `soc_top_sim_path` → `digital/rtl/demo_sram_32x256_model.v`
- `rtl_file_entries` → `['digital/rtl/demo_sram_32x256_model.v', '/root/chiploop-backend/backend/workflows/8778ea73-6136-4e5a-873d-f91f99b0be67/digital/rtl/demo_sram_32x256_model.v', '/root/chiploop-backend/backend/workflows/8778ea73-6136-4e5a-873d-f91f99b0be67/digital/rtl/demo_sram_32x256_wrapper.v', '/root/chiploop-backend/backend/workflows/8778ea73-6136-4e5a-873d-f91f99b0be67/digital/rtl/sram_mbist_demo_controller.v']`
- `cocotb_makefile_path` → `firmware/validate/Makefile`
- `cocotb_test_paths` → `['firmware/validate/test_firmware_smoke.py']`
- `validation_report_path` → `firmware/validate/validation_report.md`

## Key assumptions

- system_integration_intent_missing

## Risks / Gaps

- (none recorded)

## Next system software steps

- Consume `system_software_handoff.json` as the primary machine-readable input.
- Build the public system software package against the register map, HAL, and driver contract rather than scraping raw artifacts.
- Treat placeholder ELF as non-executable for runtime validation even if the file path exists.
- Use the runtime/simulation contract only for validation stages, not as part of the software build itself.
