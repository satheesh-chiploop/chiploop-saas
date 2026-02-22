"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Run"
      subtitle="End-to-end firmware flow with artifacts + executive summary"
      runPath="/apps/embedded/run"
    />
  );
}