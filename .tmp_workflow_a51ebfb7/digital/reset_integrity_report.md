{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 6,
  "detected_reset_signals": [
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_actuator_safety.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_mmio.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_request_fsm.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_actuator_safety.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_mmio.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_request_fsm.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a51ebfb7-58cb-4cd5-b6ef-3c5de6453605/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
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