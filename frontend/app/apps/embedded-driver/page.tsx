"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Driver"
      subtitle="Driver scaffold + ISR + DMA integration"
      runPath="/apps/embedded/driver/run"
    />
  );
}