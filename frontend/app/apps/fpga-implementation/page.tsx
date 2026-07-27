import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaImplementationPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-implementation"
      title="FPGA Implementation"
      subtitle="Run FPGA synthesis, place-and-route, timing/DRC, closure, and implementation dashboard evidence."
      runPath="/apps/fpga/implementation/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="implementation"
    />
  );
}
