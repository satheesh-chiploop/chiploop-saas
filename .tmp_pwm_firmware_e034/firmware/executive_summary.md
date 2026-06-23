# Firmware Executive Summary

## Overview
- Overall execution status: simulation_passed
- Execution readiness: ready
- Coverage available: False
- Executed tests: 1
- Passed tests: 1
- Failed tests: 0

## Artifacts produced
- firmware/register_map.json
- firmware/firmware_manifest.json
- firmware/hal/registers.rs
- firmware/hal/register_validation.md
- firmware/drivers/driver_scaffold.rs
- firmware/isr/interrupts.rs
- firmware/integration_contract.md
- firmware/build/build_instructions.md
- firmware/validate/verilator_build.md
- firmware/validate/cocotb_harness.py
- firmware/validate/Makefile
- firmware/validate/test_firmware_smoke.py
- firmware/validate/cosim_run.md
- firmware/validate/coverage.md
- firmware/validate/validation_report.md

## Key assumptions
- Coverage metrics are omitted when no executed run or real coverage artifact is present.

## Risks / Gaps
- No material gaps were detected from the currently recorded artifacts.

## Next verification steps
- Enable real coverage instrumentation before reporting percentages.
- Preserve artifact paths in state['embedded'] for reproducible downstream reporting.
