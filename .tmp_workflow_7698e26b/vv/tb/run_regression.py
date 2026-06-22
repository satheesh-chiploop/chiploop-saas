"""Regression runner for Cocotb + Verilator."""

import argparse
import json
import os
from datetime import datetime
import subprocess

DEFAULT_TESTS = [
  "smoke_test"
]

def _now():
    return datetime.now().isoformat()

def run_one(testcase: str, seed: int) -> dict:
    env = os.environ.copy()
    env["RANDOM_SEED"] = str(seed)
    cmd = [os.environ.get("CHIPLOOP_MAKE", "make"), f"TESTCASE={testcase}"]
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return {
        "testcase": testcase,
        "seed": seed,
        "ok": p.returncode == 0,
        "returncode": p.returncode,
        "stdout_tail": (p.stdout or "").splitlines()[-80:],
        "stderr_tail": (p.stderr or "").splitlines()[-80:],
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tests", nargs="+", default=DEFAULT_TESTS)
    ap.add_argument("--seeds", nargs="+", type=int, default=[1])
    ap.add_argument("--out", default="reports/regression_summary.json")
    args = ap.parse_args()

    results = []
    for t in args.tests:
        for s in args.seeds:
            results.append(run_one(t, s))

    out = {
        "type": "simulation_regression",
        "top_module": "sram_mbist_demo_controller",
        "generated_at": _now(),
        "default_tests": DEFAULT_TESTS,
        "results": results,
        "pass_count": sum(1 for r in results if r["ok"]),
        "fail_count": sum(1 for r in results if not r["ok"]),
    }

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    raise SystemExit(0 if out["fail_count"] == 0 else 2)

if __name__ == "__main__":
    main()
