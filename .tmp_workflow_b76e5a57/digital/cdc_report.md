{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 5
  },
  "observations": {
    "inferred_clocks": [],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/handoff/adaptive_aero_control_top_ip_package/rtl/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/rtl/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/rtl/pass2/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/rtl/pass3/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/b76e5a57-a5ad-4da8-8d36-c7bd3277df2d/fpga/src/upstream/adaptive_aero_control_top.v",
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