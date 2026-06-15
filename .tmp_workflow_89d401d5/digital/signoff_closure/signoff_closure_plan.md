# System PD Signoff Closure Plan

- closure_complete: `False`
- selected_restart_stage: `Analog Physical Collateral Package Agent`
- dominant_issue: `analog_lvs`
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
- `analog_lvs` from `Analog Physical Collateral Package Agent`: Repair analog SPICE/GDS pin and device correspondence, then rerun analog LVS and downstream digital signoff.

## Skipped Repairs
- `digital_drc`: Selected restart at Analog Physical Collateral Package Agent invalidates later-stage ECO; re-evaluate after rerun.
- `digital_lvs`: Selected restart at Analog Physical Collateral Package Agent invalidates later-stage ECO; re-evaluate after rerun.
- `tapeout_lec_blocked`: Blocked by earlier signoff failure; repair the upstream physical issue first.