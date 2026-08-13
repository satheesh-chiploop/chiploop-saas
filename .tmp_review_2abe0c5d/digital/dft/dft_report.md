# DFT Scan Stitching

- Status: `no_scan_flops`
- Tool: `openroad` via `none`
- PDK: `sky130A`
- DFT mode: `scan_replace_preview`
- Scan mapping: `not_applied`
- Scan-mapped flops: `0`
- Top module: `smart_sensor_hub_mcu`
- SDC: `smart_sensor_hub_mcu.sdc`
- Scan flops: `0`
- Latches: `0`
- Scan chains: `1`
- Actual scan chains: `not reported`
- Max chain length estimate: `0`
- Scan enable: `scan_en`
- Stitched netlist generated: `False`

This OpenROAD integration uses the DFT commands available in the OpenLane2 image: `set_dft_config`, `preview_dft`, and `scan_replace`.
If status is `scan_cell_mapping_required`, synthesis produced ordinary flops rather than scan flops; use a scan-cell mapping step or a private DFT adapter before ATPG.
If status is `tool_unavailable` or `tool_missing_dft_support`, install/configure OpenROAD/OpenLane2 with DFT support or map this agent to a private DFT tool adapter.
If status is `tool_needs_technology`, configure the active PDK root so OpenROAD can read technology LEF, standard-cell LEF, and Liberty files.
