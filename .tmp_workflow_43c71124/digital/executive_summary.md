# Digital Executive Summary
- workflow_id: `43c71124-316e-411a-ba15-1e794fa059b8`
- run_tag: `System_PD_43c71124-316e-411a-ba15-1e794fa059b8`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/43c71124-316e-411a-ba15-1e794fa059b8/de6a80c1-7843-495a-a19e-f72bbbbc2fce/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `253`
- Area: `3429.5392`
- Flip-flops: `65`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `-0.5233698067512442`
- TNS: `-1.4160859552453542`
- DRC violations: `429`
- DRC status: `violations_found`
- LVS status: `mismatch`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`-1.7251529582059861`, tns=`-5.413451173888797`
- sta_postplace: worst_slack=`1.51806`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`-0.5233698067512442`, tns=`-1.4160859552453542`
- sta_postfill: worst_slack=`-0.5233698067512442`, tns=`-1.4160859552453542`

## GDS Paths (local, only if produced)
- KLayout GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/43c71124-316e-411a-ba15-1e794fa059b8/de6a80c1-7843-495a-a19e-f72bbbbc2fce/digital/digital/tapeout/gds/klayout.gds`
- Magic GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/43c71124-316e-411a-ba15-1e794fa059b8/de6a80c1-7843-495a-a19e-f72bbbbc2fce/digital/digital/tapeout/gds/magic.gds`

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