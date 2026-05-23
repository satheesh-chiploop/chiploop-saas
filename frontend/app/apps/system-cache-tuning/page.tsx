"use client";

import SystemExplorerApp from "@/components/system/SystemExplorerApp";

export default function SystemCacheTuningPage() {
  return (
    <SystemExplorerApp
      title="System Cache Tuning Explorer"
      subtitle="Sweep L1/L2 cache sizes, associativity, line size, and prefetching for X86 or RISC-V workloads."
      defaultForm={{ exploration_type: "cache_tuning", isa: "x86", l1d_size_kb: [16, 32, 64, 128], l2_size_kb: [256, 512, 1024] }}
    />
  );
}
