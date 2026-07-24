import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FPGA2RTLPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga2rtl"
      title="FPGA2RTL"
      subtitle="Generate FPGA-ready RTL from design intent, create board-specific PCF/LPF constraints, then run synthesis, place-and-route, timing, and bitstream handoff."
      runPath="/apps/fpga2rtl/run"
      dashboardStage="fpga"
      fields={["source", "fpga", "frequency", "notes"]}
      defaultSourceMode="generate_arch2rtl"
      sourceModeLabel="FPGA2RTL from design intent"
    />
  );
}
