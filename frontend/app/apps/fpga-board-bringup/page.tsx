import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";

export default function FpgaBoardBringupPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-board-bringup"
      title="FPGA Board Bring-up"
      subtitle="Generate a board-matched bitstream, programming command, detection checks, and a hardware smoke-test handoff."
      runPath="/apps/fpga/board-bringup/run"
      dashboardStage="fpga"
      fields={["source", "rtl", "fpga", "frequency", "notes"]}
      defaultSourceMode="from_arch2rtl"
      fpgaMode="board-bringup"
    />
  );
}
