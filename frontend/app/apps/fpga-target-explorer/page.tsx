import DigitalReviewAppTemplate from "../digital-review/_DigitalReviewAppTemplate";
import { MINIRV_EDGE_CONTROLLER_RTL, MINIRV_EDGE_EXPLORER_NOTES, MINIRV_EDGE_TOP } from "@/lib/fpgaTargetExplorerDemo";

export default function FpgaTargetExplorerPage() {
  return (
    <DigitalReviewAppTemplate
      slug="fpga-target-explorer"
      title="FPGA Target Explorer"
      subtitle="Compare one fixed RTL design across supported FPGA families, devices, and boards. ChipLoop automatically applies synthesis/P&R closure only to targets that miss your requested frequency."
      runPath="/apps/fpga/target-explorer/run"
      dashboardStage="fpga_target_explorer"
      fields={["source", "intent", "rtl", "frequency", "recommendation", "notes"]}
      defaultSourceMode="paste"
      fpgaMode="target-explorer"
      referenceRtl={{ label: "Load MiniRV Edge Controller reference journey", rtl: MINIRV_EDGE_CONTROLLER_RTL, topModule: MINIRV_EDGE_TOP, notes: MINIRV_EDGE_EXPLORER_NOTES }}
    />
  );
}
