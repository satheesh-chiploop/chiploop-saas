{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 7,
  "detected_reset_signals": [
    "reset_n",
    "rst_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_csr.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_fsm.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_transport.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_validator.v",
      "reset": "rst_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_csr.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_fsm.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_transport.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/23df8445-70ed-4bc4-9bb2-ca69e91f0d75/fpga/src/upstream/adaptive_aero_control_validator.v",
      "reset": "rst_n",
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