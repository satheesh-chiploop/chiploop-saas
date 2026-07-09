import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function TimingDebugPage() {
  return (
    <DigitalReviewAppTemplate
      slug="timing-debug"
      title="Timing Debug"
      subtitle="Analyze timing and STA reports from synthesis or implementation, classify failures, and get focused debug actions."
      runPath="/apps/timing-debug/run"
      dashboardStage="timing_debug"
      fields={["source", "timing", "frequency", "stage", "notes"]}
    />
  );
}
