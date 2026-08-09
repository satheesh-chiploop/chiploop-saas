{
  "type": "reset_integrity_report",
  "version": "1.0",
  "rtl_file_count": 5,
  "detected_reset_signals": [],
  "async_reset_blocks": [],
  "reset_usage_locations": [],
  "findings": [
    {
      "type": "no_reset_detected",
      "severity": "warning",
      "msg": "No reset signal detected by heuristic. Consider providing explicit reset intent in spec."
    }
  ],
  "recommendations": [
    "Prefer async-assert / sync-deassert reset strategy in multi-clock designs.",
    "Ensure reset deassertion is synchronized per clock domain.",
    "Avoid mixing async and sync reset styles without clear intent.",
    "Add reset-specific assertions: no X after reset release; stable reset sequencing."
  ],
  "note": "Heuristic scan only; use signoff reset/CDC checks in enterprise flows when available."
}