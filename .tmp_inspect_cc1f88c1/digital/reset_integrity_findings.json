{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 6,
  "detected_reset_signals": [
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_actuator_control.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_control_mmio.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_request_supervisor.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_actuator_control.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_control_mmio.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/cc1f88c1-2e31-4c16-99d6-946b9edeac87/fpga/src/upstream/adaptive_aero_request_supervisor.v",
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