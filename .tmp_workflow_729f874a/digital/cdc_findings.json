{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 7
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_controller_core.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_history_sram.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_history_store.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/729f874a-aac0-4ea7-a4d8-6e987d90b564/fpga/src/upstream/adaptive_aero_mmio_csr.v",
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