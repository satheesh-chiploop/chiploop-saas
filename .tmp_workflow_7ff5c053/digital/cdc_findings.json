{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 13
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_request_response_controller.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/cfg_window_decoder.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/adaptive_request_response_controller.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/cfg_window_decoder.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/adaptive_request_response_controller.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/rtl/pass2/cfg_window_decoder.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/adaptive_request_response_controller.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/src/upstream/cfg_window_decoder.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/7ff5c053-2e86-4401-b297-fef120bbd52d/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      }
    ]
  },
  "findings": [],
  "recommendations": [
    "Provide clock_reset_arch_intent.json for higher-fidelity CDC intent (domains, allowed crossings).",
    "For single-bit control crossings: use 2-flop synchronizers.",
    "For multi-bit data: use async FIFOs or validated handshake schemes.",
    "Run a real CDC tool in enterprise flow (Questa CDC / SpyGlass CDC / VC CDC) when available."
  ],
  "note": "This agent provides intent-level CDC screening. It is not a replacement for signoff CDC tools."
}