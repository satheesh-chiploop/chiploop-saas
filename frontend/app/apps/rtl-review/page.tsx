import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function RTLReviewPage() {
  return (
    <DigitalReviewAppTemplate
      slug="rtl-review"
      title="RTL Review"
      subtitle="Review generated, purchased, or uploaded RTL for handoff readiness, coding risks, module coverage, and recommended next actions."
      runPath="/apps/rtl-review/run"
      dashboardStage="rtl_review"
      fields={["source", "rtl", "depth", "notes"]}
    />
  );
}
