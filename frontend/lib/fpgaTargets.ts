export type FpgaTargetOption = {
  key: string;
  label: string;
  detail: string;
  vendor: "Lattice" | "Gowin";
  family: string;
  tier: "production" | "beta" | "experimental" | "unavailable";
  segments: string;
  reason?: string;
};

export const FPGA_TARGET_OPTIONS: FpgaTargetOption[] = [
  { key: "icebreaker", label: "Lattice iCEBreaker", detail: "Lattice iCE40 UP5K / 5,280 cells", vendor: "Lattice", family: "iCE40", tier: "production", segments: "Education, IoT, embedded control" },
  { key: "upduino_v3", label: "Lattice UPduino v3", detail: "Lattice iCE40 UP5K / 5,280 cells", vendor: "Lattice", family: "iCE40", tier: "production", segments: "Makers, IoT, low-cost embedded" },
  { key: "icestick", label: "Lattice iCEstick", detail: "Lattice iCE40 HX1K / 1,280 cells", vendor: "Lattice", family: "iCE40", tier: "production", segments: "Education and small control" },
  { key: "ice40_hx8k_breakout", label: "Lattice iCE40 HX8K Breakout", detail: "Lattice iCE40 HX8K / 7,680 cells", vendor: "Lattice", family: "iCE40", tier: "production", segments: "General prototyping" },
  { key: "colorlight_5a_75b", label: "Lattice Colorlight 5A-75B", detail: "Lattice ECP5-25F / 24K cells", vendor: "Lattice", family: "ECP5", tier: "production", segments: "Displays, video, networking" },
  { key: "ulx3s_ecp5_45f", label: "Lattice ULX3S ECP5-45F", detail: "Lattice ECP5-45F / 44K cells", vendor: "Lattice", family: "ECP5", tier: "production", segments: "Video, soft CPUs, general prototyping" },
  { key: "orangecrab_ecp5_85f", label: "Lattice OrangeCrab ECP5-85F", detail: "Lattice ECP5-85F / 84K cells", vendor: "Lattice", family: "ECP5", tier: "production", segments: "Compute, networking, growth" },
  { key: "certus_nx_versa_40", label: "Lattice Certus-NX Versa", detail: "Lattice Certus-NX LFD2NX-40 / Experimental", vendor: "Lattice", family: "Certus-NX", tier: "experimental", segments: "Industrial, embedded, connectivity" },
  { key: "crosslink_nx_eval_40", label: "Lattice CrossLink-NX Evaluation Board", detail: "Lattice CrossLink-NX LIFCL-40 / Experimental", vendor: "Lattice", family: "CrossLink-NX", tier: "experimental", segments: "Machine vision, camera/display bridging" },
  { key: "certuspro_nx_versa_100", label: "Lattice CertusPro-NX Versa", detail: "Lattice CertusPro-NX / Awaiting open-source support", vendor: "Lattice", family: "CertusPro-NX", tier: "unavailable", segments: "Networking, infrastructure, acceleration", reason: "LFCPNX is not supported by the qualified Yosys/Project Oxide flow." },
  { key: "machxo5_nx_65t", label: "Lattice MachXO5-NX 65T", detail: "Lattice MachXO5-NX / Awaiting open-source support", vendor: "Lattice", family: "MachXO5-NX", tier: "unavailable", segments: "Secure control and platform management", reason: "Project Oxide target support is not yet qualified." },
  { key: "gowin_tang_nano_9k", label: "Gowin Tang Nano 9K", detail: "Gowin LittleBee GW1NR-9 / Beta", vendor: "Gowin", family: "LittleBee", tier: "beta", segments: "Education, IoT, low-cost embedded" },
  { key: "gowin_tang_nano_20k", label: "Gowin Tang Nano 20K", detail: "Gowin Arora II GW2AR-18C / Beta", vendor: "Gowin", family: "Arora II", tier: "beta", segments: "Video, DSP, robotics, industrial" },
  { key: "gowin_tang_primer_20k", label: "Gowin Tang Primer 20K", detail: "Gowin Arora II GW2A-18 / Beta", vendor: "Gowin", family: "Arora II", tier: "beta", segments: "Motor control, embedded compute, communications" },
  { key: "gowin_gw5a_25_starter", label: "Gowin Arora V GW5A-25 Starter", detail: "Gowin Arora V / Awaiting upstream qualification", vendor: "Gowin", family: "Arora V", tier: "unavailable", segments: "Vision, display, DSP, edge processing", reason: "The exact GW5A-25 target and board pin map are not qualified upstream." },
  { key: "gowin_gw5at_60_pcie", label: "Gowin Arora V GW5AT-60 PCIe", detail: "Gowin Arora V / Awaiting hard-IP qualification", vendor: "Gowin", family: "Arora V", tier: "unavailable", segments: "PCIe, SerDes, networking", reason: "PCIe/SerDes are not qualified in the open-source flow." },
  { key: "gowin_gw5ast_138", label: "Gowin Arora V GW5AST-138", detail: "Gowin Arora V / Awaiting SoC qualification", vendor: "Gowin", family: "Arora V", tier: "unavailable", segments: "RISC-V, edge AI, industrial compute", reason: "Hardened RISC-V support is not qualified in Project Apicula." },
  { key: "gowin_gw3a_20k", label: "Gowin Arora III GW3A-20K", detail: "Gowin Arora III / Awaiting upstream support", vendor: "Gowin", family: "Arora III", tier: "unavailable", segments: "Industrial, vision, display, DSP", reason: "No qualified upstream Apicula implementation database yet." },
];

export const FPGA_RUNNABLE_TARGET_OPTIONS = FPGA_TARGET_OPTIONS.filter((target) => target.tier !== "unavailable");
