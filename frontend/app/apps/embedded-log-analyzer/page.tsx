"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded Log Analyzer"
      subtitle="Logs → fault classification → root cause → fix plan"
      runPath="/apps/embedded/log-analyzer/run"
    />
  );
}