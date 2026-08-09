# Simulation Summary + Coverage

- Total simulation runs: 2
- Simulation pass count: 2
- Simulation fail count: 0
- Coverage status: ok
- Functional coverage %: 59.38
- Coverage bins hit: 19
- Coverage total bins: 32
- Functional bin gaps: 10
- Code line coverage: 48.36%
- Code branch coverage: 6.16%
- Code condition coverage: 6.16%
- Code toggle coverage: 10.86%
- SVA/assertion status: missing
- SVA/assertion pass %: missing
- Formal status: not_enabled
- Golden model status: not_enabled
- Simulator tool: verilator
- Code coverage tool: verilator_coverage
- Formal tool: none
- Golden model tool: none

## Functional Coverage Not Met
- outputs._ready: bins 0/2, missing zero, nonzero, seen values []
- outputs.actuator_cmd: bins 1/2, missing nonzero, seen values [0]
- outputs.model_req_data: bins 1/2, missing nonzero, seen values [0]
- outputs.model_req_valid: bins 1/2, missing nonzero, seen values [0]
- outputs.model_rsp_ready: bins 1/2, missing nonzero, seen values [0]
- outputs.safe_state: bins 1/2, missing zero, seen values [3, 7]
- inputs._re: bins 0/2, missing zero, nonzero, seen values []
- inputs._we: bins 0/2, missing zero, nonzero, seen values []
- inputs.clk: bins 1/2, missing zero, seen values [1]
- inputs.reset_n: bins 1/2, missing zero, seen values [1]
