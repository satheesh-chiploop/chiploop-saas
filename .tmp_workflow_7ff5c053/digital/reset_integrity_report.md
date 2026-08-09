{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 13,
  "detected_reset_signals": [
    "reset_n",
    "rst_n"
  ],
  "async_reset_blocks": [
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/cfg_window_decoder.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/cfg_window_decoder.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/cfg_window_decoder.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "edge": "negedge"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/cfg_window_decoder.v",
      "reset": "rst_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/cfg_window_decoder.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/cfg_window_decoder.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/cfg_window_decoder.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/adaptive_request_response_controller.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/cfg_window_decoder.v",
      "reset": "rst_n",
      "context": "if_condition"
    },
    {
      "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
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