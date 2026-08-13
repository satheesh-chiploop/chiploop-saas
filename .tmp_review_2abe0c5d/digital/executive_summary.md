# Digital Executive Summary
- workflow_id: `2abe0c5d-7ac4-43fe-8031-ae931b35b29f`
- run_tag: `Digital_Arch2Tapeout_2abe0c5d-7ac4-43fe-8031-ae931b35b29f`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/2abe0c5d-7ac4-43fe-8031-ae931b35b29f/b4a2d3ee-d6f5-41d7-8ee3-2683e506f826/digital/arch2tapeout/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `81`
- Area: `304.0416`
- Flip-flops: `0`
- Latches: `0`
- STA stage used: `sta_postplace`
- Worst slack: `1000000000000000000000000000000000000000`
- TNS: `0`
- DRC violations: `None`
- DRC status: `failed`
- LVS status: `failed`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `not_applicable`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`1000000043329398900000000000000000000000`, tns=`0`
- sta_postplace: worst_slack=`1000000000000000000000000000000000000000`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`None`, tns=`None`
- sta_postfill: worst_slack=`None`, tns=`None`

## GDS Paths (local, only if produced)
- KLayout GDS: `None`
- Magic GDS: `None`

## Artifact Map
- synth_metrics: `digital/synth/metrics.json`
- sta_preplace_metrics: `digital/sta_preplace/metrics.json`
- sta_postplace_metrics: `digital/sta_postplace/metrics.json`
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