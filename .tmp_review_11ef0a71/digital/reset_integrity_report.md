{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 3,
  "detected_reset_signals": [
    "reset_n",
    "rst_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/11ef0a71-eb09-426d-9e7f-8e35ba118b9c/fpga/src/upstream/adaptive_aero_control_top.v",
      "reset": "rst_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/11ef0a71-eb09-426d-9e7f-8e35ba118b9c/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/11ef0a71-eb09-426d-9e7f-8e35ba118b9c/fpga/src/upstream/adaptive_aero_control_top.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/11ef0a71-eb09-426d-9e7f-8e35ba118b9c/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    }
  ],
  "findings": [],
  "recommendations": [
    "Prefer async-assert / sync-deassert reset strategy in multi-clock designs.",
    "Ensure reset deassertion is synchronized per clock domain.",
    "Avoid mixing async and sync reset styles without clear intent.",
    "Add reset-specific assertions: no X after reset release; stable reset sequencing."
  ],
  "note": "Heuristic scan only; use signoff reset/CDC checks in enterprise flows when available."
}