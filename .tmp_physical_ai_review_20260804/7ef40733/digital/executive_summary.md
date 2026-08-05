# Digital Executive Summary
- workflow_id: `7ef40733-5be0-4054-8943-441591ec8735`
- run_tag: `Digital_Arch2Tapeout_7ef40733-5be0-4054-8943-441591ec8735`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/7ef40733-5be0-4054-8943-441591ec8735/832e1f5a-553d-4e98-be44-98e4f24c4ae9/digital/arch2tapeout/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `None`
- Area: `None`
- Flip-flops: `None`
- Latches: `None`
- STA stage used: `None`
- Worst slack: `None`
- TNS: `None`
- DRC violations: `None`
- DRC status: `None`
- LVS status: `None`
- Tapeout status: `None`
- Tapeout LEC status: `incomplete_inputs`
- ATPG status: `incomplete_inputs`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`None`, tns=`None`
- sta_postplace: worst_slack=`None`, tns=`None`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`None`, tns=`None`
- sta_postfill: worst_slack=`None`, tns=`None`

## GDS Paths (local, only if produced)
- KLayout GDS: `None`
- Magic GDS: `None`

## Artifact Map
- synth_metrics: `None`
- sta_preplace_metrics: `None`
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