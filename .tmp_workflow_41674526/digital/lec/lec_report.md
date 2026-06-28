# Logic Equivalence Check

- Status: `incomplete_stdcell_models`
- Tool: `yosys`
- Top module: `uart_packet_engine`
- RTL files: `1`
- Synth netlist: `uart_packet_engine_synth.v`
- Liberty files discovered: `1`
- Standard-cell Verilog models loaded: `1`
- Standard-cell model strategy: `generated_functional_wrappers_from_gate_netlist`
- Missing standard-cell models: `1`
- Unproven points: `0`
- Unproven signal names: `none`
- Primary LEC status: `inconclusive`
- Primary unproven signal names: `none`
- Reset-sequence repair: `not_run`
- Return code: `None`
- Failure reason: `standard_cell_verilog_models_incomplete`

If this is inconclusive, inspect `digital/lec/logs/yosys_lec.log` and `digital/lec/lec_summary.json` for unsupported cells, black boxes, reset/initial-state assumptions, or bounded sequential proof limits.

## Missing Standard-Cell Models

- `sky130_fd_sc_hd__conb_1`
