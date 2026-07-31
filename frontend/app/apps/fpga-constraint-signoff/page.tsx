import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaConstraintSignoffPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-constraint-signoff"
      title="FPGA Constraint + CDC/RDC Signoff"
      subtitle="Check clocks, board I/O constraints, clock-domain crossings, reset crossings, and unconstrained paths before implementation."
      runPath="/apps/fpga/constraint-signoff/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="constraint-signoff"
    />
  );
}
