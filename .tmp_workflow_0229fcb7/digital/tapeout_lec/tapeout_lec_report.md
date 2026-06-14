# Tapeout Logic Equivalence Check

- Status: `inconclusive`
- Comparison: `RTL vs final tapeout implementation netlist`
- Top module: `pwm_controller`
- RTL files: `2`
- Tapeout netlist: `pwm_controller.pnl.v`
- Ignored physical-only gate ports: `VGND, VPWR`
- Standard-cell models loaded: `1`
- Missing standard-cell models: `0`
- Unproven points: `28`
- Return code: `1`
- Failure reason: `equivalence_points_unproven`

This is distinct from synthesis LEC. Synthesis LEC compares RTL against `digital/synth/netlist/*_synth.v`; tapeout LEC compares RTL against the final implementation netlist collected after physical implementation.
