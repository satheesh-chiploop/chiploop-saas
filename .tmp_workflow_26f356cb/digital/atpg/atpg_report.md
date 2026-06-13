# Scan ATPG Coverage

- Status: `adapter_completed_no_patterns`
- Tool: `atalanta`
- Input netlist: `scan_stitched_netlist.v`
- Generated bench: `generated`
- Pattern count: `0`
- Stuck-at coverage: `not reported`
- Faults detected: `not reported`
- Faults undetected: `not reported`
- Faults aborted: `not reported`

A configured ATPG adapter must write `atpg_metrics.json` with real pattern and coverage metrics. Runs without that file are reported as `adapter_completed_no_metrics`; zero-pattern metrics are reported as `adapter_completed_no_patterns`.
If status is `wrong_tool_detected`, the executable name matched but the binary is not a digital ATPG tool.
