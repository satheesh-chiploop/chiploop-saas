# Digital Executive Summary
- workflow_id: `30734adb-33b9-4000-8b0e-a911961bac0f`
- run_tag: `Digital_Arch2Tapeout_30734adb-33b9-4000-8b0e-a911961bac0f`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/30734adb-33b9-4000-8b0e-a911961bac0f/a3d869e5-ee6f-4838-9460-66c7ab5ff8f1/digital/arch2tapeout/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `None`
- Area: `None`
- Flip-flops: `None`
- Latches: `None`
- STA stage used: `sta_preplace`
- Worst slack: `4.5915272883390275`
- TNS: `0`
- DRC violations: `None`
- DRC status: `failed`
- LVS status: `failed`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`4.5915272883390275`, tns=`0`
- sta_postplace: worst_slack=`None`, tns=`None`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`None`, tns=`None`
- sta_postfill: worst_slack=`None`, tns=`None`

## GDS Paths (local, only if produced)
- KLayout GDS: `None`
- Magic GDS: `None`

## Artifact Map
- synth_metrics: `None`
- sta_preplace_metrics: `digital/sta_preplace/metrics.json`
- sta_postplace_metrics: `None`
- sta_postcts_metrics: `None`
- sta_postroute_metrics: `None`
- sta_postfill_metrics: `None`
- drc_metrics: `None`
- lvs_metrics: `None`
- tapeout_metrics: `None`

## Next Iteration Suggestions
- If worst_slack < 0: relax constraints or improve synthesis/placement/CTS/route parameters.
- If DRC violations > 0: inspect DRC logs and rerun with adjusted floorplan/route settings.
- If LVS not clean: check extraction/streamout mismatch and netlist naming.