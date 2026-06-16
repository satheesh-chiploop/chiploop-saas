# System PD Signoff Closure Plan

- closure_complete: `False`
- selected_restart_stage: `Digital LVS Agent`
- dominant_issue: `digital_lvs`
- max_iterations: `1`
- stop_reason: `repair_plan_created`

## Post-Fill Timing
- setup WNS: `0`
- setup TNS: `0`
- setup violations: `0`
- hold WNS: `0`
- hold TNS: `0`
- hold violations: `0`

## Repair Actions
- `digital_lvs` from `Digital LVS Agent`: Repair extracted-vs-source netlist or pin/cell mismatch, then rerun LVS and tapeout signoff.

## Skipped Repairs
- `tapeout_lec_blocked`: Blocked by earlier signoff failure; repair the upstream physical issue first.