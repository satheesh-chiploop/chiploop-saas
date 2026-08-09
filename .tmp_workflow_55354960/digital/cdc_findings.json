{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 4
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/adaptive_aero_control_top.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/rtl/pass2/adaptive_aero_control_top.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/55354960-e951-42a6-95bc-dffb4e4dd8b7/fpga/src/upstream/adaptive_aero_control_top.v",
        "clock": "clk",
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