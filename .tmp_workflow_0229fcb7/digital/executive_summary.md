# Digital Executive Summary
- workflow_id: `0229fcb7-ede5-4185-95d5-2deefa86134d`
- run_tag: `Digital_Arch2Tapeout_0229fcb7-ede5-4185-95d5-2deefa86134d`
- run_work_dir: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/0229fcb7-ede5-4185-95d5-2deefa86134d/0ac7a25b-9f47-49dd-8c66-c437397a9518/digital/arch2tapeout/digital/run_work`

## Key Metrics (best-effort parsed)
- Cell count: `147`
- Area: `1915.5872`
- Flip-flops: `33`
- Latches: `0`
- STA stage used: `sta_postfill`
- Worst slack: `15.63143614346702`
- TNS: `0`
- DRC violations: `0`
- DRC status: `clean`
- LVS status: `clean`
- Tapeout status: `ok`
- Tapeout LEC status: `inconclusive`
- ATPG status: `patterns_generated`
- Summary status: `failed`

## STA Stage Breakdown
- sta_preplace: worst_slack=`15.256583983544719`, tns=`0`
- sta_postplace: worst_slack=`17.7817`, tns=`0`
- sta_postcts: worst_slack=`None`, tns=`None`
- sta_postroute: worst_slack=`15.63143614346702`, tns=`0`
- sta_postfill: worst_slack=`15.63143614346702`, tns=`0`

## GDS Paths (local, only if produced)
- KLayout GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/0229fcb7-ede5-4185-95d5-2deefa86134d/0ac7a25b-9f47-49dd-8c66-c437397a9518/digital/arch2tapeout/digital/tapeout/gds/klayout.gds`
- Magic GDS: `/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/0229fcb7-ede5-4185-95d5-2deefa86134d/0ac7a25b-9f47-49dd-8c66-c437397a9518/digital/arch2tapeout/digital/tapeout/gds/magic.gds`

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