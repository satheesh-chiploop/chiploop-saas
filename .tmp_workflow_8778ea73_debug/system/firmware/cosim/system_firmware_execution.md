# System Firmware CoSim Execution Summary

- Generated at: 2026-06-22T19:07:37.466732
- Execution mode: runtime_execution
- Overall status: simulation_passed
- Readiness: ready

## Key Inputs

- SoC top: `digital/rtl/demo_sram_32x256_model.v`
- Firmware ELF: `firmware/build/target/x86_64-unknown-linux-gnu/release/firmware_app.elf`
- Cocotb Makefile: `firmware/validate/Makefile`
- Test files: `1`
- Verilog/SystemVerilog files: `3`

## Planned Test Matrix

- test_firmware_smoke.py | seed=1 | status=passed
- test_firmware_smoke.py | seed=2 | status=planned

## Notes

- Runtime execution was requested and attempted with the discovered cocotb collateral.
- No coverage model detected; downstream summary should avoid reporting functional coverage percentages.
- No digital assertions collateral detected; assertion coverage should remain unavailable, not fabricated.
- Firmware ELF was detected for firmware-aware co-simulation.

## Conclusion

Runtime execution completed successfully with the discovered co-simulation collateral.
