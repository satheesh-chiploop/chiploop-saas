# Logic Equivalence Check

- Status: `pass`
- Tool: `yosys`
- Top module: `smart_sensor_hub_mcu`
- RTL files: `1`
- Synth netlist: `smart_sensor_hub_mcu_synth.v`
- Liberty files discovered: `1`
- Standard-cell Verilog models loaded: `1`
- Standard-cell model strategy: `generated_functional_wrappers_from_gate_netlist`
- Missing standard-cell models: `0`
- Unproven points: `0`
- Unproven signal names: `none`
- Primary LEC status: `pass`
- Primary unproven signal names: `none`
- Reset-sequence repair: `not_run`
- Return code: `0`
- Failure reason: `equivalence_proven`

If this is inconclusive, inspect `digital/lec/logs/yosys_lec.log` and `digital/lec/lec_summary.json` for unsupported cells, black boxes, reset/initial-state assumptions, or bounded sequential proof limits.
