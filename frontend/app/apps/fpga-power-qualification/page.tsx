import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaPowerQualificationPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-power-qualification"
      title="FPGA Power + Device Qualification"
      subtitle="Qualify device fit, implementation headroom, support tier, target frequency, and an early-stage transparent power estimate."
      runPath="/apps/fpga/power-qualification/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="power-qualification"
    />
  );
}
