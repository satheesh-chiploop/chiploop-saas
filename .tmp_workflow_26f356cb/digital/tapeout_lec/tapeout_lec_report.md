# Tapeout Logic Equivalence Check

- Status: `incomplete_stdcell_models`
- Comparison: `RTL vs final tapeout implementation netlist`
- Top module: `temp_monitor_soc_phys`
- RTL files: `4`
- Tapeout netlist: `temp_monitor_soc_phys.pnl.v`
- Ignored physical-only gate ports: `VGND, VPWR`
- Standard-cell models loaded: `1`
- Missing standard-cell models: `1`
- Unproven points: `0`
- Return code: `None`
- Failure reason: `standard_cell_verilog_models_incomplete`

This is distinct from synthesis LEC. Synthesis LEC compares RTL against `digital/synth/netlist/*_synth.v`; tapeout LEC compares RTL against the final implementation netlist collected after physical implementation.
