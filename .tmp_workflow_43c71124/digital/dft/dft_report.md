# DFT Scan Stitching

- Status: `scan_replace_pass`
- Tool: `openroad` via `openlane2_docker`
- PDK: `sky130A`
- DFT mode: `scan_replace_preview`
- Scan mapping: `mapped`
- Scan-mapped flops: `64`
- Top module: `temp_monitor_soc_phys`
- SDC: `top.sdc`
- Scan flops: `65`
- Latches: `0`
- Scan chains: `4`
- Actual scan chains: `4`
- Max chain length estimate: `17`
- Scan enable: `scan_en`
- Stitched netlist generated: `True`

This OpenROAD integration uses the DFT commands available in the OpenLane2 image: `set_dft_config`, `preview_dft`, and `scan_replace`.
If status is `scan_cell_mapping_required`, synthesis produced ordinary flops rather than scan flops; use a scan-cell mapping step or a private DFT adapter before ATPG.
If status is `tool_unavailable` or `tool_missing_dft_support`, install/configure OpenROAD/OpenLane2 with DFT support or map this agent to a private DFT tool adapter.
If status is `tool_needs_technology`, configure the active PDK root so OpenROAD can read technology LEF, standard-cell LEF, and Liberty files.
