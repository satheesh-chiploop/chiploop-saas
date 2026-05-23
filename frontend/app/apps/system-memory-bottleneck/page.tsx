"use client";

import SystemExplorerApp from "@/components/system/SystemExplorerApp";

export default function SystemMemoryBottleneckPage() {
  return (
    <SystemExplorerApp
      title="System Memory Bottleneck Explorer"
      subtitle="Sweep memory presets, cache sizes, and cores to classify cache-bound vs memory-bound behavior."
      defaultForm={{
        exploration_type: "memory_bottleneck",
        isa: "riscv",
        memory_types: ["DDR3_1600_8x8", "DDR4_2400_8x8", "LPDDR5_5500_1x16"],
        l1d_size_kb: [32, 64],
        l2_size_kb: [512, 1024],
        cores: 2,
      }}
    />
  );
}
