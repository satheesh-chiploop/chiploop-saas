{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 3,
  "detected_reset_signals": [
    "reset_n",
    "soft_reset_req"
  ],
  "async_reset_blocks": [
    {
      "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/sram_mbist_demo_controller.v",
      "reset": "reset_n",
      "edge": "negedge"
    }
  ],
  "reset_usage_locations": [
    {
      "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/sram_mbist_demo_controller.v",
      "reset": "reset_n",
      "context": "if_condition"
    },
    {
      "file": "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/75353468-4063-4dba-985b-9f52fce5c333/6fa89d8f-31f2-4bef-a686-8ab7fccd6f8c/digital/dqa/handoff/rtl/sram_mbist_demo_controller.v",
      "reset": "soft_reset_req",
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