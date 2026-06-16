# Digital Executive Summary
- workflow_id: `e6ffce8d-17d7-4511-aae3-34c953406829`
- run_tag: `System_PD_e6ffce8d-17d7-4511-aae3-34c953406829`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e6ffce8d-17d7-4511-aae3-34c953406829/aea4e7a4-8d37-486d-86c2-cd3dcc00ee22/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `253`
- Area: `3429.5392`
- Flip-flops: `65`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `0.03181988096410438`
- TNS: `0`
- DRC violations: `None`
- DRC status: `blackbox_deferred`
- LVS status: `blackbox_deferred`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`-1.0171530572378826`, tns=`-2.7959910733625404`
- sta_postplace: worst_slack=`2.23627`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`0.03181988096410438`, tns=`0`
- sta_postfill: worst_slack=`0.03181988096410438`, tns=`0`

## GDS Paths (local, only if produced)
- KLayout GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e6ffce8d-17d7-4511-aae3-34c953406829/aea4e7a4-8d37-486d-86c2-cd3dcc00ee22/digital/digital/tapeout/gds/klayout.gds`
- Magic GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e6ffce8d-17d7-4511-aae3-34c953406829/aea4e7a4-8d37-486d-86c2-cd3dcc00ee22/digital/digital/tapeout/gds/magic.gds`

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