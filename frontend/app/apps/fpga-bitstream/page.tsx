import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaBitstreamPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-bitstream"
      title="FPGA RTL to Bitstream"
      subtitle="Prototype existing RTL on iCE40/ECP5 (Lattice FPGA families) targets using verification, open-source synthesis, place-and-route, timing, and bitstream handoff."
      runPath="/apps/fpga/bitstream/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "verify", "frequency", "notes"]}
    />
  );
}
