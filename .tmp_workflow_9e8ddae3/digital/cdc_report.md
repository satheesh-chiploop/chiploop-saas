{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 9
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_command_safety.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_control_csr_mmio.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_request_engine.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_response_validator.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/adaptive_aero_status_telemetry.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/9e8ddae3-e03a-445c-8121-f02792ae17ac/fpga/src/upstream/fpga_bram_512x32.v",
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