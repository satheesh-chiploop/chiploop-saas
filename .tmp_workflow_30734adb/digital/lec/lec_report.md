# Logic Equivalence Check

- Status: `inconclusive`
- Tool: `yosys`
- Top module: `AeroGuard_Active_Aerodynamics_Controller`
- RTL files: `5`
- Synth netlist: `AeroGuard_Active_Aerodynamics_Controller_synth.v`
- Liberty files discovered: `1`
- Standard-cell Verilog models loaded: `1`
- Standard-cell model strategy: `generated_functional_wrappers_from_gate_netlist`
- Missing standard-cell models: `0`
- Unproven points: `0`
- Unproven signal names: `none`
- Primary LEC status: `inconclusive`
- Primary unproven signal names: `none`
- Reset-sequence repair: `not_run`
- Return code: `None`
- Failure reason: `yosys_inconclusive_see_lec_log`

If this is inconclusive, inspect `digital/lec/logs/yosys_lec.log` and `digital/lec/lec_summary.json` for unsupported cells, black boxes, reset/initial-state assumptions, or bounded sequential proof limits.
