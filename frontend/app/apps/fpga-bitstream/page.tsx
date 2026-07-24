import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaBitstreamPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-bitstream"
      title="FPGA RTL to Bitstream"
      subtitle="Prototype existing RTL on iCE40 or ECP5 FPGA targets using open-source synthesis, place-and-route, timing, and bitstream handoff."
      runPath="/apps/fpga/bitstream/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
    />
  );
}
