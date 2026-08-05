# Logic Equivalence Check

- Status: `incomplete_inputs`
- Tool: `yosys`
- Top module: `aero_safety_controller`
- RTL files: `4`
- Synth netlist: `missing`
- Liberty files discovered: `1`
- Standard-cell Verilog models loaded: `1`
- Standard-cell model strategy: `pdk_stdcell_verilog`
- Missing standard-cell models: `0`
- Unproven points: `0`
- Unproven signal names: `none`
- Primary LEC status: `inconclusive`
- Primary unproven signal names: `none`
- Reset-sequence repair: `not_run`
- Return code: `None`
- Failure reason: `missing_synthesized_netlist`

If this is inconclusive, inspect `digital/lec/logs/yosys_lec.log` and `digital/lec/lec_summary.json` for unsupported cells, black boxes, reset/initial-state assumptions, or bounded sequential proof limits.
