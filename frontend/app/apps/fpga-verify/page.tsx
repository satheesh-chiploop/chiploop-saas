import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaVerifyPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-verify"
      title="FPGA Verify"
      subtitle="Run FPGA-focused testbench, assertions, simulation, coverage, optional formal checks, and closure loop on generated or existing RTL."
      runPath="/apps/fpga/verify/run"
      closureRunPath="/apps/fpga/verify/closure-loop/run"
      dashboardStage="verification"
      fields={["source", "rtl", "verify", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="verify"
    />
  );
}
