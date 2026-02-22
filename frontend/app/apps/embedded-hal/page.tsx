"use client";
import EmbeddedAppTemplate from "../embedded/_EmbeddedAppTemplate";

export default function Page() {
  return (
    <EmbeddedAppTemplate
      title="Embedded HAL"
      subtitle="Register extraction → Rust HAL layer → validation"
      runPath="/apps/embedded/hal/run"
    />
  );
}