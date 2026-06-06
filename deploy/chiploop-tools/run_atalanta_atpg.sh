#!/usr/bin/env bash
set -euo pipefail

: "${CHIPLOOP_ATPG_STAGE_DIR:?missing CHIPLOOP_ATPG_STAGE_DIR}"
: "${CHIPLOOP_ATPG_INPUT_NETLIST:?missing CHIPLOOP_ATPG_INPUT_NETLIST}"
: "${CHIPLOOP_ATPG_METRICS_JSON:?missing CHIPLOOP_ATPG_METRICS_JSON}"
: "${CHIPLOOP_ATPG_PATTERNS_DIR:?missing CHIPLOOP_ATPG_PATTERNS_DIR}"

ATALANTA_BIN="${CHIPLOOP_ATALANTA:-/usr/local/bin/atalanta}"
if ! command -v "$ATALANTA_BIN" >/dev/null 2>&1; then
  echo "atalanta not found at CHIPLOOP_ATALANTA=$ATALANTA_BIN" >&2
  exit 127
fi

mkdir -p "$CHIPLOOP_ATPG_PATTERNS_DIR"

BENCH_FILE="${CHIPLOOP_ATPG_BENCH_FILE:-}"
if [[ -z "$BENCH_FILE" ]]; then
  echo "No Atalanta .bench file was provided." >&2
  echo "Set CHIPLOOP_ATPG_BENCH_FILE to a real full-scan combinational .bench file." >&2
  echo "Input scan netlist staged by ChipLoop: $CHIPLOOP_ATPG_INPUT_NETLIST" >&2
  exit 2
fi

if [[ ! -f "$BENCH_FILE" ]]; then
  echo "Configured CHIPLOOP_ATPG_BENCH_FILE does not exist: $BENCH_FILE" >&2
  exit 2
fi

OUT_LOG="$CHIPLOOP_ATPG_STAGE_DIR/atalanta.out"
PATTERN_FILE="$CHIPLOOP_ATPG_PATTERNS_DIR/atalanta.test"

"$ATALANTA_BIN" -t "$PATTERN_FILE" "$BENCH_FILE" > "$OUT_LOG" 2>&1

python3 - "$OUT_LOG" "$PATTERN_FILE" "$CHIPLOOP_ATPG_METRICS_JSON" <<'PY'
import json
import re
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
pattern_path = Path(sys.argv[2])
metrics_path = Path(sys.argv[3])
text = log_path.read_text(encoding="utf-8", errors="ignore")

def num(patterns):
    for pattern in patterns:
        match = re.search(pattern, text, flags=re.IGNORECASE)
        if match:
            value = float(match.group(1))
            return int(value) if value.is_integer() else value
    return None

pattern_count = num([
    r"Number\s+of\s+test\s+patterns\s*:?\s*([0-9]+)",
    r"test\s+patterns\s*:?\s*([0-9]+)",
])
coverage = num([
    r"Fault\s+coverage\s*:?\s*([0-9]+(?:\.[0-9]+)?)\s*%",
    r"coverage\s*:?\s*([0-9]+(?:\.[0-9]+)?)\s*%",
])
collapsed = num([r"Number\s+of\s+collapsed\s+faults\s*:?\s*([0-9]+)", r"collapsed\s+faults\s*:?\s*([0-9]+)"])
redundant = num([r"Number\s+of\s+identified\s+redundant\s+faults\s*:?\s*([0-9]+)", r"redundant\s+faults\s*:?\s*([0-9]+)"])
aborted = num([r"Number\s+of\s+aborted\s+faults\s*:?\s*([0-9]+)", r"aborted\s+faults\s*:?\s*([0-9]+)"])

if pattern_count is None and pattern_path.exists():
    pattern_count = sum(1 for line in pattern_path.read_text(encoding="utf-8", errors="ignore").splitlines() if re.match(r"^\s*[01xX]+\s*$", line))

metrics = {
    "pattern_count": pattern_count,
    "stuck_at_coverage_pct": coverage,
    "faults_detected": None,
    "faults_undetected": None,
    "faults_aborted": aborted,
    "collapsed_faults": collapsed,
    "redundant_faults": redundant,
    "atalanta_output": str(log_path),
    "pattern_file": str(pattern_path),
}
if pattern_count is None and coverage is None:
    raise SystemExit("Atalanta completed but no pattern count or coverage was found in output.")
metrics_path.write_text(json.dumps(metrics, indent=2), encoding="utf-8")
PY
