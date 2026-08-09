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
        "file": "backend/workflows/a371458b-e094-4745-8b94-94125198585e/fpga/src/handoff/pwm_fpga_demo_ip_package/rtl/pwm_fpga_demo.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a371458b-e094-4745-8b94-94125198585e/fpga/src/rtl/pwm_fpga_demo.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a371458b-e094-4745-8b94-94125198585e/handoff/pwm_fpga_demo_ip_package/rtl/pwm_fpga_demo.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a371458b-e094-4745-8b94-94125198585e/rtl/pwm_fpga_demo.v",
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