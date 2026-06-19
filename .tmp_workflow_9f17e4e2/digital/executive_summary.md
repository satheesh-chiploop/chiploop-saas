# Digital Executive Summary
- workflow_id: `9f17e4e2-4c7c-47d3-a9ba-4d09c2f00169`
- run_tag: `System_PD_9f17e4e2-4c7c-47d3-a9ba-4d09c2f00169`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/9f17e4e2-4c7c-47d3-a9ba-4d09c2f00169/fb1e0dee-ceb5-417a-900a-47409d974a5c/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `253`
- Area: `3429.5392`
- Flip-flops: `65`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `-0.006375788966136975`
- TNS: `-0.006375788966136975`
- DRC violations: `0`
- DRC status: `clean`
- LVS status: `failed`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`-1.0171530572378826`, tns=`-2.7959910733625404`
- sta_postplace: worst_slack=`2.24119`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`-0.006375788966136975`, tns=`-0.006375788966136975`
- sta_postfill: worst_slack=`-0.006375788966136975`, tns=`-0.006375788966136975`

## GDS Paths (local, only if produced)
- KLayout GDS: `None`
- Magic GDS: `None`

## Artifact Map
- synth_metrics: `digital/synth/metrics.json`
- sta_preplace_metrics: `digital/sta_preplace/metrics.json`
- sta_postplace_metrics: `digital/sta_postplace/metrics.json`
- sta_postcts_metrics: `None`
- sta_postroute_metrics: `digital/sta_postroute/metrics.json`
- sta_postfill_metrics: `digital/sta_postfill/metrics.json`
- drc_metrics: `None`
- lvs_metrics: `None`
- tapeout_metrics: `None`

## Next Iteration Suggestions
- If worst_slack < 0: relax constraints or improve synthesis/placement/CTS/route parameters.
- If DRC violations > 0: inspect DRC logs and rerun with adjusted floorplan/route settings.
- If LVS not clean: check extraction/streamout mismatch and netlist naming.