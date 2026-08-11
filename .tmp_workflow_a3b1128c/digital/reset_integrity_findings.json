{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 11,
  "detected_reset_signals": [
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_clamper.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_tx.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/command_validator.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/control_register_bank.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/fallback_fsm.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/status_telemetry.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/stream_rx.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/timeout_monitor.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_clamper.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_tx.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/command_validator.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/control_register_bank.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/fallback_fsm.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/status_telemetry.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/stream_rx.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/timeout_monitor.v",
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