{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 4,
  "detected_reset_signals": [
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/pass2/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/upstream/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/pass2/adaptive_aero_control_top.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/upstream/adaptive_aero_control_top.v",
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