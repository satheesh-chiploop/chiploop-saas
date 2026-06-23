# Simulation Summary + Coverage

- Total simulation runs: 12
- Simulation pass count: 8
- Simulation fail count: 4
- Coverage status: ok
- Functional coverage %: 75.0
- Coverage bins hit: 15
- Coverage total bins: 20
- Functional bin gaps: 5
- Code line coverage: 21.74%
- Code branch coverage: 0.0%
- Code condition coverage: 0.0%
- Code toggle coverage: 1.74%
- SVA/assertion status: ok
- SVA/assertion pass %: 100.0%
- Formal status: pass
- Golden model status: generated
- Simulator tool: verilator
- Code coverage tool: verilator_coverage
- Formal tool: symbiyosys
- Golden model tool: chiploop_python_scoreboard

## Functional Coverage Not Met
- outputs.counter_value: bins 1/2, missing nonzero, seen values [0]
- outputs.pwm_out: bins 1/2, missing nonzero, seen values [0]
- outputs.rd_data: bins 1/2, missing nonzero, seen values [0]
- inputs.clk: bins 1/2, missing zero, seen values [1]
- inputs.reset_n: bins 1/2, missing zero, seen values [1]
