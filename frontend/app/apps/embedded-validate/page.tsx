"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Validate"
      subtitle="RTL + firmware co-simulation + coverage + report"
      runPath="/apps/embedded/validate/run"
    />
  );
}