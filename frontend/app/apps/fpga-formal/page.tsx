import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaFormalPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-formal"
      title="FPGA Formal"
      subtitle="Run FPGA-focused SymbiYosys formal checks on generated, pasted, or repository RTL."
      runPath="/apps/fpga/formal/run"
      dashboardStage="verification"
      fields={["source", "rtl", "verify", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="formal"
    />
  );
}
