{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 7,
  "detected_reset_signals": [
    "reset",
    "reset_n"
  ],
  "async_reset_blocks": [],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_registers.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_registers.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_request_packager.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_response_parser.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_supervisor.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/f0aefe85-b5c0-4c9a-b352-28b45f77c68e/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
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