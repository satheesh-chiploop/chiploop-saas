"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Diagnostics"
      subtitle="Register dump + BIST + stress tools"
      runPath="/apps/embedded/diagnostics/run"
    />
  );
}