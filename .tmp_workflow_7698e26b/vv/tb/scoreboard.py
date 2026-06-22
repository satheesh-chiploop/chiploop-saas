"""Auto-generated Scoreboard + Golden Model hooks for sram_mbist_demo_controller"""

import os
import json
from dataclasses import dataclass
from typing import Any, Dict, List
import cocotb
from cocotb.triggers import RisingEdge, Timer

TOP = "sram_mbist_demo_controller"
CLK = null

@dataclass
class Txn:
    inputs: Dict[str, int]
    outputs: Dict[str, int]
    time_ns: int

def golden_model(txn: Txn) -> Dict[str, int]:
    """Pure-Python reference model placeholder (implement from spec)."""
    return dict(txn.outputs)

class Scoreboard:
    def __init__(self, dut):
        self.dut = dut
        self.mismatches: List[Dict[str, Any]] = []
        self.enabled = False
        self.input_ports = []
        self.output_ports = []

    def start(self):
        self.enabled = True
        cocotb.start_soon(self._run())

    def stop(self):
        self.enabled = False
        self._write_report()

    async def _run(self):
        if CLK:
            while self.enabled:
                await RisingEdge(getattr(self.dut, CLK))
                self.observe()
        else:
            while self.enabled:
                await Timer(10, units="ns")
                self.observe()

    def _snapshot(self) -> Txn:
        inp = {}
        out = {}
        for n in self.input_ports:
            try: inp[n] = int(getattr(self.dut, n).value)
            except Exception: pass
        for n in self.output_ports:
            try: out[n] = int(getattr(self.dut, n).value)
            except Exception: pass
        return Txn(inputs=inp, outputs=out, time_ns=0)

    def observe(self):
        if not self.enabled:
            return
        txn = self._snapshot()
        exp = golden_model(txn)
        for k, vexp in exp.items():
            vobs = txn.outputs.get(k)
            if vobs is None:
                continue
            if int(vobs) != int(vexp):
                self.mismatches.append({
                    "signal": k,
                    "expected": int(vexp),
                    "observed": int(vobs),
                    "inputs": txn.inputs,
                })

    def _write_report(self):
        rep_dir = os.path.join(os.path.dirname(__file__), "reports")
        os.makedirs(rep_dir, exist_ok=True)
        out = {
            "type": "golden_model_comparison",
            "top_module": TOP,
            "mismatch_count": len(self.mismatches),
            "mismatches": self.mismatches[:200],
        }
        with open(os.path.join(rep_dir, "scoreboard_report.json"), "w", encoding="utf-8") as f:
            json.dump(out, f, indent=2)
