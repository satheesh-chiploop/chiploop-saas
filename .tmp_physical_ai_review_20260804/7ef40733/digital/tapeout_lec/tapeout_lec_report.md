# Tapeout Logic Equivalence Check

- Status: `incomplete_inputs`
- Comparison: `rtl_vs_tapeout_netlist`
- Top module: `aero_safety_controller`
- Reference netlist: `RTL inputs`
- RTL files: `4`
- Tapeout netlist: `missing`
- Ignored physical-only gate ports: `none`
- Ignored reference-only scan ports: `none`
- Standard-cell models loaded: `1`
- Missing standard-cell models: `0`
- Unproven points: `0`
- Return code: `None`
- Failure reason: `missing_synthesized_netlist`

This is distinct from synthesis LEC. Tapeout LEC compares the final implementation netlist against the closest available proven reference netlist, falling back to RTL only when no gate reference exists.
