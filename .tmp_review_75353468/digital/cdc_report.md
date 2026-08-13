{
  "type": "cdc_analysis_report",
  "version": "1.0",
  "inputs": {
    "clock_reset_intent_present": false,
    "rtl_file_count": 3
  },
  "observations": {
    "inferred_clocks": [
      "clk"
    ],
    "inferred_domains": [],
    "per_file": [
      {
        "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/demo_sram_32x256_model.v",
        "clock": "clk",
        "domain": null
      },
      {
        "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/demo_sram_32x256_wrapper.v",
        "clock": null,
        "domain": null
      },
      {
        "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/sram_mbist_demo_controller.v",
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