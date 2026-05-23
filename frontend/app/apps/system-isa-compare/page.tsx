"use client";

import SystemExplorerApp from "@/components/system/SystemExplorerApp";

export default function SystemIsaComparePage() {
  return (
    <SystemExplorerApp
      title="System ISA Compare"
      subtitle="Compare X86 and RISC-V behavior for the same workload and cache/memory settings."
      defaultForm={{ exploration_type: "isa_compare", isa: "x86", isas: ["x86", "riscv"], l1d_size_kb: [32, 64], l2_size_kb: [512, 1024] }}
    />
  );
}
