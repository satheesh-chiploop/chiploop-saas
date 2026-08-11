{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 6,
  "detected_reset_signals": [
    "cfg_seq_reset",
    "reset",
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_actuator.v",
      "reset": "reset",
      "edge": "posedge"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_mmio.v",
      "reset": "reset",
      "edge": "posedge"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_transport.v",
      "reset": "reset",
      "edge": "posedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_actuator.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_mmio.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_transport.v",
      "reset": "reset",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/006fa69f-6ebe-4543-b006-692612697070/fpga/src/upstream/adaptive_aero_control_top_transport.v",
      "reset": "cfg_seq_reset",
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