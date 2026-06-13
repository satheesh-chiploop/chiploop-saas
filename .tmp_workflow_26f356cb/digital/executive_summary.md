# Digital Executive Summary
- workflow_id: `26f356cb-6d29-43be-a1da-649876540ea6`
- run_tag: `System_PD_26f356cb-6d29-43be-a1da-649876540ea6`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/26f356cb-6d29-43be-a1da-649876540ea6/6d479abf-c006-4bf3-b6cb-21bcf6d57fc4/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `376`
- Area: `4659.4688`
- STA stage used: `sta_postplace`
- Worst slack: `15.824`
- TNS: `0`
- DRC violations: `None`
- DRC status: `failed`
- LVS status: `failed`
- Tapeout status: `failed`
- Tapeout LEC status: `incomplete_stdcell_models`
- ATPG status: `adapter_completed_no_patterns`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`11.247683991438404`, tns=`0`
- sta_postplace: worst_slack=`15.824`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`None`, tns=`None`

## GDS Paths (local, only if produced)
- KLayout GDS: `None`
- Magic GDS: `None`

## Artifact Map
- synth_metrics: `digital/synth/metrics.json`
- sta_preplace_metrics: `digital/sta_preplace/metrics.json`
- sta_postplace_metrics: `digital/sta_postplace/metrics.json`
- sta_postcts_metrics: `None`
- sta_postroute_metrics: `None`
- drc_metrics: `None`
- lvs_metrics: `None`
- tapeout_metrics: `None`

## Next Iteration Suggestions
- If worst_slack < 0: relax constraints or improve synthesis/placement/CTS/route parameters.
- If DRC violations > 0: inspect DRC logs and rerun with adjusted floorplan/route settings.
- If LVS not clean: check extraction/streamout mismatch and netlist naming.