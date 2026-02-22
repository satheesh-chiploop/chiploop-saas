"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Boot"
      subtitle="Boot sequencing + PLL + reset + power modes"
      runPath="/apps/embedded/boot/run"
    />
  );
}