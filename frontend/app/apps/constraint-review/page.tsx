import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function ConstraintReviewPage() {
  return (
    <DigitalReviewAppTemplate
      slug="constraint-review"
      title="Constraint Review"
      subtitle="Check SDC coverage against RTL clock intent before synthesis, STA, or tapeout."
      runPath="/apps/constraint-review/run"
      dashboardStage="constraint_review"
      fields={["source", "rtl", "sdc", "frequency", "notes"]}
    />
  );
}
