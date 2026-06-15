# Digital Executive Summary
- workflow_id: `919478b7-46be-40fa-8ff0-688455fbfa56`
- run_tag: `System_PD_919478b7-46be-40fa-8ff0-688455fbfa56`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/919478b7-46be-40fa-8ff0-688455fbfa56/bd979697-7a54-4d39-b158-657e0fb25348/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `253`
- Area: `3429.5392`
- Flip-flops: `65`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `14.24906810652235`
- TNS: `0`
- DRC violations: `535`
- DRC status: `violations_found`
- LVS status: `mismatch`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`13.982847275829034`, tns=`0`
- sta_postplace: worst_slack=`17.2189`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`14.24906810652235`, tns=`0`
- sta_postfill: worst_slack=`14.24906810652235`, tns=`0`

## GDS Paths (local, only if produced)
- KLayout GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/919478b7-46be-40fa-8ff0-688455fbfa56/bd979697-7a54-4d39-b158-657e0fb25348/digital/digital/tapeout/gds/klayout.gds`
- Magic GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/919478b7-46be-40fa-8ff0-688455fbfa56/bd979697-7a54-4d39-b158-657e0fb25348/digital/digital/tapeout/gds/magic.gds`

## Artifact Map
- synth_metrics: `digital/synth/metrics.json`
- sta_preplace_metrics: `digital/sta_preplace/metrics.json`
- sta_postplace_metrics: `digital/sta_postplace/metrics.json`
- sta_postcts_metrics: `None`
- sta_postroute_metrics: `digital/sta_postroute/metrics.json`
- sta_postfill_metrics: `digital/sta_postfill/metrics.json`
- drc_metrics: `None`
- lvs_metrics: `None`
- tapeout_metrics: `digital/tapeout/metrics.json`

## Next Iteration Suggestions
- If worst_slack < 0: relax constraints or improve synthesis/placement/CTS/route parameters.
- If DRC violations > 0: inspect DRC logs and rerun with adjusted floorplan/route settings.
- If LVS not clean: check extraction/streamout mismatch and netlist naming.