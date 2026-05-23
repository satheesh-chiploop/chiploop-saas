"use client";

import SystemExplorerApp from "@/components/system/SystemExplorerApp";

export default function SystemCpuModelPage() {
  return (
    <SystemExplorerApp
      title="System CPU Model Explorer"
      subtitle="Compare TimingSimpleCPU, MinorCPU, and O3CPU for fast exploration versus detailed analysis."
      defaultForm={{ exploration_type: "cpu_model", isa: "x86", cpu_models: ["TimingSimpleCPU", "MinorCPU", "O3CPU"], l1d_size_kb: [32, 64], l2_size_kb: [512] }}
    />
  );
}
