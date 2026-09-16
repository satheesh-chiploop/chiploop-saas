{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 7,
  "detected_reset_signals": [
    "reset_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/actuator_command_limiter.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/aero_history_logger.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/aero_transport_fsm.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/control_validation_core.v",
      "reset": "reset_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/domino_surrogate_interface.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/actuator_command_limiter.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/adaptive_aero_control_top_spi_fpga_top.sv",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/aero_history_logger.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/aero_transport_fsm.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/control_validation_core.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7b39e309-9409-4b7f-849b-071acd7a0a45/fpga/src/handoff/rtl/domino_surrogate_interface.v",
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