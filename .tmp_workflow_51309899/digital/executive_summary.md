# Digital Executive Summary
- workflow_id: `51309899-ca8a-4d6b-9dea-fe920ed5245a`
- run_tag: `System_PD_51309899-ca8a-4d6b-9dea-fe920ed5245a`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/51309899-ca8a-4d6b-9dea-fe920ed5245a/dcd843f9-fbf5-4346-87d3-d80a96d61c3d/digital/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `376`
- Area: `4659.4688`
- Flip-flops: `80`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `12.297279098640987`
- TNS: `0`
- DRC violations: `432`
- DRC status: `violations_found`
- LVS status: `completed_with_deferred_xor_error`
- Tapeout status: `failed`
- Tapeout LEC status: `blocked`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`11.249326233382876`, tns=`0`
- sta_postplace: worst_slack=`15.912`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`12.297279098640987`, tns=`0`
- sta_postfill: worst_slack=`12.297279098640987`, tns=`0`

## GDS Paths (local, only if produced)
- KLayout GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/51309899-ca8a-4d6b-9dea-fe920ed5245a/dcd843f9-fbf5-4346-87d3-d80a96d61c3d/digital/digital/tapeout/gds/klayout.gds`
- Magic GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/51309899-ca8a-4d6b-9dea-fe920ed5245a/dcd843f9-fbf5-4346-87d3-d80a96d61c3d/digital/digital/tapeout/gds/magic.gds`

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