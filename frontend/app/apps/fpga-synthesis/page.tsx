import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaSynthesisPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-synthesis"
      title="FPGA Synthesis"
      subtitle="Run RTL quality, board constraints, Yosys FPGA synthesis, and synthesis closure evidence."
      runPath="/apps/fpga/synthesis/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="synthesis"
    />
  );
}
