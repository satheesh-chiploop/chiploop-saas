# System PD Signoff Closure Plan

- closure_complete: `False`
- selected_restart_stage: `Digital Floorplan Agent`
- dominant_issue: `digital_drc`
- max_iterations: `1`
- stop_reason: `repair_plan_created`

## Post-Fill Timing
- setup WNS: `-0.5233698067512442`
- setup TNS: `-1.4160859552453542`
- setup violations: `12`
- hold WNS: `0`
- hold TNS: `0`
- hold violations: `0`

## Repair Actions
- `digital_drc` from `Digital Floorplan Agent`: Classify DRC categories, apply the corresponding floorplan/route/fill ECO, then rerun from the selected physical stage.
- `digital_lvs` from `Digital Floorplan Agent`: Repair extracted-vs-source netlist or pin/cell mismatch, then rerun LVS and tapeout signoff.

## Skipped Repairs
- `setup_timing`: Selected restart at Digital Floorplan Agent invalidates later-stage ECO; re-evaluate after rerun.
- `tapeout_lec_blocked`: Blocked by earlier signoff failure; repair the upstream physical issue first.