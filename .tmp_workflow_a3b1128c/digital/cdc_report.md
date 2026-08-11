{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 11
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/fpga/target_explorer/interface_adapter/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_clamper.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/actuator_tx.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/adaptive_aero_control_top.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/adaptive_aero_control_top_spi_fpga_top.sv",
        "clock": null,
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/command_validator.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/control_register_bank.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/fallback_fsm.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/status_telemetry.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/stream_rx.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "backend/workflows/a3b1128c-fe93-4b9d-99aa-2cae3d164049/fpga/src/upstream/timeout_monitor.v",
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