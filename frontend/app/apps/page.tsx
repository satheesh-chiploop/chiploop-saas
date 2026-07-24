"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { apiDelete, apiGet, apiPatch, apiPost } from "@/lib/apiClient";
import { LowCreditBanner } from "@/components/PlanCreditStatus";
import TopNav from "@/components/TopNav";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  FPGA_BITSTREAM_PREFILL_KEY,
  IMAGE_DMA_PIPELINE_ARCH2RTL_SPEC,
  MBIST_SRAM_ARCH2RTL_SPEC,
  PWM_FPGA_ICEBREAKER_PCF,
  PWM_FPGA_RTL_TEXT,
  PWM_FULL_STACK_ARCH2RTL_SPEC,
  SAFETY_FAULT_MANAGER_ARCH2RTL_SPEC,
  SECURE_BOOT_ARCH2RTL_SPEC,
  SENSOR_HUB_ARCH2RTL_SPEC,
  SYSTEM_MIXED_SIGNAL_PREFILL_KEY,
  TEMP_MONITOR_SYSTEM_ANALOG_SPEC,
  TEMP_MONITOR_SYSTEM_DIGITAL_SPEC,
  TEMP_MONITOR_SYSTEM_SOC_SPEC,
  UART_PACKET_ENGINE_ARCH2RTL_SPEC,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();

type LoopType = "digital" | "validation" | "analog" | "embedded" | "system" | "fpga";

const LOOP_TYPES: LoopType[] = ["digital", "fpga", "analog", "system", "embedded", "validation"];
type CatalogView = "home" | "digital" | "fpga" | "system" | "analog" | "embedded" | "validation";

type OnboardingResponse = {
  status: string;
  onboarding: {
    completed: boolean;
    completed_at?: string | null;
    skipped_at?: string | null;
  };
};

const ONBOARDING_DEMO_KEY = "chiploop_arch2rtl_onboarding_demo";

const ARCH2RTL_ONBOARDING_SPEC = `Design a parameterized PWM controller.

Inputs:
- clk
- reset_n
- enable
- duty_cycle[7:0]
- period[7:0]

Outputs:
- pwm_out
- counter_value[7:0]

Behavior:
- Counter increments every clock when enable is high.
- Counter resets to zero when it reaches period.
- pwm_out is high when counter_value is less than duty_cycle.
- All registers reset to zero when reset_n is low.

Generate synthesizable SystemVerilog, timing constraints, UPF-lite power intent, and a handoff package.`;

type AppCard = {
  slug: string;
  title: string;
  subtitle: string;
  loop_type: LoopType;
  status?: "Flagship" | "New" | "Coming";
  nudge?: string;
  promise?: string;
};

type UserApp = {
  id: string;
  workflow_id: string;
  workflow_name?: string | null;
  name: string;
  slug?: string | null;
  description?: string | null;
  category?: LoopType | string | null;
  loop_type?: LoopType | string | null;
  visibility?: string | null;
  status?: string | null;
  marketplace_status?: string | null;
  price_usd?: number | null;
  created_at?: string | null;
};

type UserAppsResponse = {
  status: string;
  apps: UserApp[];
};

type ReferenceJourney = {
  key: string;
  exploreTitle: string;
  segment: string;
  title: string;
  copy: string;
  button: string;
  onClick: () => void;
  stages?: string[];
};

const LOOP_META: Record<LoopType, {
  title: string;
  tagline: string;
  icon: string;
  accent: string;
  softBg: string;
  border: string;
}> = {
  digital: {
    title: "Digital Loop",
    tagline: "Design to RTL to verify to improve",
    icon: "D",
    accent: "bg-sky-400",
    softBg: "bg-sky-500/10 text-sky-200",
    border: "border-sky-500/30",
  },
  fpga: {
    title: "FPGA Loop",
    tagline: "Prototype RTL to bitstream to board handoff",
    icon: "F",
    accent: "bg-lime-300",
    softBg: "bg-lime-500/10 text-lime-100",
    border: "border-lime-500/30",
  },
  validation: {
    title: "Validation Loop",
    tagline: "Plan to run to learn to improve",
    icon: "V",
    accent: "bg-amber-300",
    softBg: "bg-amber-500/10 text-amber-100",
    border: "border-amber-500/30",
  },
  analog: {
    title: "Analog Loop",
    tagline: "Analyze to simulate to correlate to improve",
    icon: "A",
    accent: "bg-fuchsia-400",
    softBg: "bg-fuchsia-500/10 text-fuchsia-200",
    border: "border-fuchsia-500/30",
  },
  embedded: {
    title: "Embedded Firmware Loop",
    tagline: "Code to run to observe to fix",
    icon: "E",
    accent: "bg-emerald-400",
    softBg: "bg-emerald-500/10 text-emerald-200",
    border: "border-emerald-500/30",
  },
  system: {
    title: "System Loop",
    tagline: "Integrate to analyze to optimize",
    icon: "S",
    accent: "bg-cyan-300",
    softBg: "bg-cyan-500/10 text-cyan-100",
    border: "border-cyan-500/30",
  },
};

export default function AppsHomePage() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);
  const [onboardingLoading, setOnboardingLoading] = useState(true);
  const [onboardingComplete, setOnboardingComplete] = useState(true);
  const [onboardingBusy, setOnboardingBusy] = useState(false);
  const [myApps, setMyApps] = useState<UserApp[]>([]);
  const [myAppsLoading, setMyAppsLoading] = useState(false);
  const [submittingAppId, setSubmittingAppId] = useState<string | null>(null);
  const [editingAppId, setEditingAppId] = useState<string | null>(null);
  const [editAppDraft, setEditAppDraft] = useState<Partial<UserApp>>({});
  const [deletingAppId, setDeletingAppId] = useState<string | null>(null);

  const [catalogView, setCatalogView] = useState<CatalogView>("home");
  const [selectedReferenceJourney, setSelectedReferenceJourney] = useState<string | null>(null);

  useEffect(() => {
    let mounted = true;
    (async () => {
      const { data: { user } } = await supabase.auth.getUser();
      if (!mounted) return;
      setUserEmail(user?.email ?? null);

      if (!user) {
        setOnboardingComplete(true);
        setOnboardingLoading(false);
        return;
      }

      setMyAppsLoading(true);
      apiGet<UserAppsResponse>("/studio/user-apps")
        .then((response) => {
          if (mounted) setMyApps(response.apps || []);
        })
        .catch(() => {
          if (mounted) setMyApps([]);
        })
        .finally(() => {
          if (mounted) setMyAppsLoading(false);
        });

      try {
        const response = await apiGet<OnboardingResponse>("/settings/onboarding");
        if (!mounted) return;
        setOnboardingComplete(Boolean(response.onboarding.completed));
      } catch {
        if (!mounted) return;
        setOnboardingComplete(true);
      } finally {
        if (mounted) setOnboardingLoading(false);
      }
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    const loop = new URLSearchParams(window.location.search).get("loop");
    if (LOOP_TYPES.includes(loop as LoopType)) {
      setCatalogView(loop as CatalogView);
    }
  }, []);

  useEffect(() => {
    if (onboardingLoading || window.location.hash !== "#reference-journeys") return;
    window.setTimeout(() => {
      document.getElementById("reference-journeys")?.scrollIntoView({ behavior: "smooth", block: "start" });
    }, 0);
  }, [onboardingLoading]);

  // Apps are grouped by loop so the page can present both guided entry points and full catalog sections.
  const apps: AppCard[] = useMemo(() => ([
    {
      slug: "ask-project",
      title: "Ask this Project",
      subtitle: "Chat with uploaded files, codebases, specs, reports, logs, and docs",
      loop_type: "system",
      status: "New",
      nudge: "Project review",
      promise: "Summaries, risks, suggestions, and recommended next workflows",
    },
    {
      slug: "validation-run",
      title: "Validation Run",
      subtitle: "One-click run on real hardware with preflight + learning",
      loop_type: "validation",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Get run results + gaps + exec report",
    },

    // Digital apps
    {
      slug: "arch2rtl",
      title: "Arch2RTL",
      subtitle: "Spec to Architecture to Microarch to RTL to Handoff package",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Most used",
      promise: "Generate RTL + docs + handoff artifacts",
    },
    {
      slug: "spec2rtl",
      title: "Spec2RTL Check",
      subtitle: "Check generated or third-party RTL against a claimed spec",
      loop_type: "digital",
      status: "New",
      nudge: "Conformance",
      promise: "Report matched, partial, missing, and inconclusive requirements",
    },
    {
      slug: "rtl-review",
      title: "RTL Review",
      subtitle: "Review RTL handoff readiness, coding risks, and module coverage",
      loop_type: "digital",
      status: "New",
      nudge: "Code review",
      promise: "Find RTL risks before verification or implementation",
    },
    {
      slug: "constraint-review",
      title: "Constraint Review",
      subtitle: "Check SDC coverage against RTL clock intent",
      loop_type: "digital",
      status: "New",
      nudge: "Timing setup",
      promise: "Catch missing clocks, IO delays, and exception risks",
    },
    {
      slug: "timing-debug",
      title: "Timing Debug",
      subtitle: "Analyze STA reports and classify timing failures",
      loop_type: "digital",
      status: "New",
      nudge: "Closure",
      promise: "Get focused setup, hold, constraint, and fanout actions",
    },
    {
      slug: "arch2synthesis",
      title: "Arch2Synthesis",
      subtitle: "Arch2RTL + Synthesis (or RTL to Synthesis) with reports",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Fast path",
      promise: "Get clean netlist + timing/area/power reports",
    },
    
    {
      slug: "arch2tapeout",
      title: "Arch2Tapeout",
      subtitle: "Arch2RTL + Synthesis + RTL->GDS pipeline (partial runs supported)",
      loop_type: "digital",
      status: "Flagship",
      nudge: "End-to-end",
      promise: "Run RTL->GDS with DRC/LVS/Tapeout + exec summary",
    },
    {
      slug: "dqa",
      title: "DQA",
      subtitle: "CDC + RDC + Lint + Synthesis readiness quality gate",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Catch issues before tape-in",
    },
    {
      slug: "fpga-bitstream",
      title: "FPGA RTL to Bitstream",
      subtitle: "Run FPGA synthesis, place-and-route, timing, and bitstream handoff",
      loop_type: "fpga",
      status: "New",
      nudge: "Prototype",
      promise: "Generate FPGA implementation evidence and programming handoff",
    },
    {
      slug: "fpga2rtl",
      title: "FPGA2RTL",
      subtitle: "Generate FPGA-ready RTL and board-specific PCF/LPF constraints from design intent",
      loop_type: "fpga",
      status: "New",
      nudge: "Design intent",
      promise: "Start FPGA prototyping even when RTL is not available",
    },
    {
      slug: "verify",
      title: "Verify",
      subtitle: "Testbench + Coverage + SVA + Simulation summary",
      loop_type: "digital",
      status: "Flagship",
      nudge: "New",
      promise: "Generate verification environment fast",
    },
    {
      slug: "smoke",
      title: "Smoke",
      subtitle: "Fast compile + quick sim + triage pack",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Quick confidence the RTL isn't broken",
    },
    {
      slug: "integrate",
      title: "Integrate",
      subtitle: "Text to Integration intent to Top RTL + report",
      loop_type: "digital",
      status: "Flagship",
      nudge: "New",
      promise: "Assemble IPs into a runnable top",
    },

    {
      slug: "validation-plan",
      title: "Validation Plan & Coverage",
      subtitle: "Datasheet/spec to test plan + coverage map + gaps",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Structured plan + coverage gaps in one shot",
    },
    {
      slug: "bench-setup",
      title: "Bench Setup",
      subtitle: "Register instruments to create bench to schematic to preflight",
      loop_type: "validation",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Get bench ready fast with clean artifacts",
    },
    {
      slug: "preflight",
      title: "Preflight Only",
      subtitle: "Quick readiness validation without running tests",
      loop_type: "validation",
      status: "Flagship",
      nudge: "Most used",
      promise: "Rapid bench sanity check + summary",
    },
    {
      slug: "validation-insights",
      title: "Validation Insights",
      subtitle: "Analyze past runs to patterns to evolve plan + coverage",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Turn history into next test improvements",
    },

    // Analog apps
    {
      slug: "analog-run",
      title: "Analog Run",
      subtitle: "Spec to Netlist to Model to Validate to Correlate to Iterate",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Recommended",
      promise: "End-to-end analog loop",
    },
    {
      slug: "analog-spec",
      title: "Analog Spec",
      subtitle: "Text to structured spec + open questions",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Most used",
      promise: "Clean spec JSON",
    },
    {
      slug: "analog-netlist",
      title: "Analog Netlist",
      subtitle: "Spec to SPICE scaffold + sim plan",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "Netlist + sim plan",
    },
    {
      slug: "analog-model",
      title: "Analog Model",
      subtitle: "Spec to SV RNM / Verilog-A behavioral model",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Most used",
      promise: "Fast system model",
    },
    {
      slug: "analog-validate-model",
      title: "Model Validation",
      subtitle: "TB + SVA + coverage intent for model",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Validate behavior",
    },
    {
      slug: "analog-correlate",
      title: "Correlate",
      subtitle: "Behavioral vs netlist correlation report",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "Quantify model deltas",
    },
    {
      slug: "analog-iterate",
      title: "Iterate",
      subtitle: "Patch proposals + next run plan",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "Improve model",
    },
    {
      slug: "analog-abstracts",
      title: "Abstract Views",
      subtitle: "LEF + LIB stub + integration notes",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "PnR/STA handoff",
    },   

    // Embedded apps
    {
      slug: "embedded-run",
      title: "Embedded Run",
      subtitle: "End-to-end firmware flow: HAL to Drivers to Boot to Diagnostics to Co-sim to Report",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Production-ready firmware package + exec summary",
    },
    {
      slug: "embedded-hal",
      title: "Embedded HAL",
      subtitle: "Register extraction to Rust HAL layer to validation",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Rust register abstraction (HAL)",
    },
    {
      slug: "embedded-driver",
      title: "Embedded Driver",
      subtitle: "Driver scaffold + ISR + DMA integration",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Drivers package + integration contract",
    },
    {
      slug: "embedded-boot",
      title: "Embedded Boot",
      subtitle: "Boot sequencing + PLL + reset + power modes",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Boot plan + init code + timing checks",
    },
    {
      slug: "embedded-diagnostics",
      title: "Embedded Diagnostics",
      subtitle: "Register dump + BIST + stress tools",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Diagnostics toolkit + summary",
    },
    {
      slug: "embedded-log-analyzer",
      title: "Embedded Log Analyzer",
      subtitle: "Logs to fault classification to root cause to fix plan",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Root-cause and recommended actions",
    },
    {
      slug: "embedded-validate",
      title: "Embedded Validate",
      subtitle: "RTL + firmware co-simulation + coverage + report",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "New",
      promise: "Co-sim results + coverage report",
    },
    // System apps
    {
      slug: "system-end2end",
      title: "System End2End",
      subtitle: "Digital + Analog + SoC integration to Sim + PD + Firmware to ZIP",
      loop_type: "system",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Tapeout-ready SoC package + reports",
    },
    {
      slug: "system-sim",
      title: "System Sim",
      subtitle: "Integrate SoC + run simulation + coverage + waveforms",
      loop_type: "system",
      status: "Flagship",
      nudge: "Most used",
      promise: "Simulation report + coverage + waves",
    },
    {
      slug: "system-verify",
      title: "System Verify",
      subtitle: "System-level test intent, simulation, coverage, formal options, and debug evidence",
      loop_type: "system",
      status: "Flagship",
      nudge: "Recommended",
      promise: "System verification dashboard + coverage evidence",
    },
    {
      slug: "system-architecture",
      title: "System Architecture Explorer",
      subtitle: "No-code gem5 workload/cache sweeps with performance, power, area, and charts",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Visual PPA tradeoffs without writing gem5 configs",
    },
    {
      slug: "architecture-to-rtl",
      title: "Architecture-to-RTL Delivery",
      subtitle: "Turn completed gem5 architecture results into reviewed Arch2RTL intent and traceability",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Bridge system evidence into RTL handoff",
    },
    {
      slug: "system-cache-tuning",
      title: "System Cache Tuning",
      subtitle: "Tune L1/L2 cache, associativity, line size, and prefetching on X86/RISC-V",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Find the cache knee for a workload",
    },
    {
      slug: "system-isa-compare",
      title: "System ISA Compare",
      subtitle: "Compare X86 and RISC-V behavior for the same workload and memory hierarchy",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Normalize performance, power, and cache behavior",
    },
    {
      slug: "system-memory-bottleneck",
      title: "System Memory Bottleneck",
      subtitle: "Sweep memory presets, cores, and cache sizes to classify bottlenecks",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Find cache-bound vs memory-bound behavior",
    },
    {
      slug: "system-cpu-model",
      title: "System CPU Model",
      subtitle: "Compare TimingSimpleCPU, MinorCPU, and O3CPU exploration tradeoffs",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Choose fast vs detailed CPU modeling",
    },
    {
      slug: "system-dqa",
      title: "System DQA",
      subtitle: "System RTL quality gate with lint, CDC, reset integrity, and synthesis readiness",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Quality checks on integrated System RTL",
    },
    {
      slug: "system-synthesis",
      title: "System Synthesis",
      subtitle: "System RTL through synthesis, LEC, scan DFT, ATPG, and MBIST evidence",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "System netlist + LEC/DFT/ATPG evidence",
    },
    {
      slug: "system-pd",
      title: "System PD",
      subtitle: "System RTL2GDS with synthesis, STA, DRC/LVS/XOR, tapeout, and tapeout LEC",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "GDS + signoff-gated DRC/LVS/XOR/LEC evidence",
    },
    {
      slug: "system-rtl",
      title: "System RTL Handoff",
      subtitle: "Digital + Analog + SoC intent to integrated top RTL + handoff package",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Generate integrated system RTL + top assembly artifacts",
    },
    {
      slug: "system-firmware",
      title: "System Firmware",
      subtitle: "Register extract to driver scaffold to build to co-sim results",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Firmware drivers + co-sim report",
    },
    {
      slug: "system-software",
      title: "System Software",
      subtitle: "Firmware handoff to SDK to API to applications",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Generate SDK + APIs + software package",
    },
    {
      slug: "system-software-validation",
      title: "System Software Validation",
      subtitle: "Validate software package or run full software to firmware to RTL co-simulation",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Build + test + contract + package validation or full co-sim proof",
    },
    {
      slug: "system-product-builder",
      title: "Product App Builder",
      subtitle: "Turn validated RTL, firmware, software, and validation collateral into a simulator-backed app",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Runnable dashboard + simulator adapter + product package",
    },

  ]), []);

  const featuredApps = ["arch2rtl", "system-rtl", "system-synthesis", "system-verify"]
    .map((slug) => apps.find((app) => app.slug === slug))
    .filter((app): app is AppCard => Boolean(app));

  const outcomeInputs: Record<LoopType, string> = {
    digital: "Architecture spec or RTL",
    fpga: "RTL, board target, and PCF constraints",
    analog: "Analog spec or netlist",
    embedded: "Registers, firmware intent, or logs",
    validation: "Datasheet, bench, or run intent",
    system: "SoC intent, subsystem specs, or handoff package",
  };

  const outcomeOutputs: Record<LoopType, string> = {
    digital: "RTL, reports, constraints, and ZIP package",
    fpga: "JSON netlist, place-and-route, timing report, and bitstream package",
    analog: "Models, correlation reports, and integration views",
    embedded: "HAL, drivers, diagnostics, and co-sim proof",
    validation: "Plans, run results, gaps, and executive report",
    system: "Integrated top, simulation evidence, firmware, and reports",
  };

  const go = (path: string) => router.push(path);

  async function startArch2RtlOnboarding() {
    setOnboardingBusy(true);
    try {
      window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
        projectName: "pwm_controller_onboarding",
        topModule: "pwm_controller",
        designLanguage: "systemverilog",
        specText: ARCH2RTL_ONBOARDING_SPEC,
        toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
      }));
      await apiPost("/settings/onboarding", {
        action: "start",
        last_step: "arch2rtl_demo_started",
        metadata: { demo: "arch2rtl", source: "apps_onboarding" },
      });
      go("/apps/arch2rtl?guided=1");
    } catch {
      go("/apps/arch2rtl?guided=1");
    } finally {
      setOnboardingBusy(false);
    }
  }

  function startPwmFullStackDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "pwm_controller_onboarding",
      topModule: "pwm_controller",
      designLanguage: "systemverilog",
      specText: PWM_FULL_STACK_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "pwm" }));
    go("/apps/arch2rtl?guided=1&pwm_chain=1");
  }

  function startPwmFpgaPrototypeDemo() {
    window.localStorage.setItem(FPGA_BITSTREAM_PREFILL_KEY, JSON.stringify({
      rtlSourceMode: "paste",
      rtlText: PWM_FPGA_RTL_TEXT,
      board: "icebreaker",
      topModule: "pwm_fpga_demo",
      targetFrequency: "12",
      pcfText: PWM_FPGA_ICEBREAKER_PCF,
      notes: "Reference journey: PWM RTL generation to FPGA synthesis, place-and-route, timing, and bitstream handoff.",
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "pwm_fpga_prototype" }));
    go("/apps/fpga-bitstream?guided=1&pwm_fpga=1");
  }

  function startUartPacketDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "uart_packet_engine_demo",
      topModule: "uart_packet_engine",
      designLanguage: "systemverilog",
      specText: UART_PACKET_ENGINE_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "uart_packet" }));
    go("/apps/arch2rtl?guided=1&uart_chain=1");
  }

  function startImageDmaDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "image_dma_pipeline_demo",
      topModule: "image_dma_pipeline",
      designLanguage: "systemverilog",
      specText: IMAGE_DMA_PIPELINE_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "image_dma" }));
    go("/apps/arch2rtl?guided=1&image_chain=1");
  }

  function startMbistSramDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "sram_mbist_demo",
      topModule: "sram_mbist_demo_controller",
      designLanguage: "systemverilog",
      specText: MBIST_SRAM_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true, insertMbist: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "mbist_sram" }));
    go("/apps/arch2rtl?guided=1&mbist_chain=1");
  }

  function startSensorHubDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "smart_sensor_hub_mcu_demo",
      topModule: "smart_sensor_hub_mcu",
      designLanguage: "systemverilog",
      specText: SENSOR_HUB_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "sensor_hub" }));
    go("/apps/arch2rtl?guided=1&sensor_chain=1");
  }

  function startSecureBootDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "secure_boot_key_manager_demo",
      topModule: "secure_boot_key_manager",
      designLanguage: "systemverilog",
      specText: SECURE_BOOT_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "secure_boot" }));
    go("/apps/arch2rtl?guided=1&secure_chain=1");
  }

  function startSafetyFaultDemo() {
    window.localStorage.setItem(ONBOARDING_DEMO_KEY, JSON.stringify({
      projectName: "safety_fault_watchdog_demo",
      topModule: "safety_fault_watchdog",
      designLanguage: "systemverilog",
      specText: SAFETY_FAULT_MANAGER_ARCH2RTL_SPEC,
      toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "safety_fault" }));
    go("/apps/arch2rtl?guided=1&safety_chain=1");
  }

  function startTempMonitorSystemDemo() {
    window.localStorage.setItem(SYSTEM_MIXED_SIGNAL_PREFILL_KEY, JSON.stringify({
      projectName: "temp_monitor_mixed_signal_soc",
      topModule: "temp_monitor_soc",
      digitalSpecText: TEMP_MONITOR_SYSTEM_DIGITAL_SPEC,
      analogSpecText: TEMP_MONITOR_SYSTEM_ANALOG_SPEC,
      socIntegrationSpecText: TEMP_MONITOR_SYSTEM_SOC_SPEC,
      runSpec2RtlCheck: true,
      systemSimTestcases: "reset_defaults, threshold_below, threshold_above, alert_clear",
      systemSimSeeds: "1, 2, 7",
      systemSimNumIters: 40,
    }));
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify({ demoKind: "temp_monitor_system" }));
    go("/apps/system-rtl?tempmon_chain=1");
  }

  const openApp = (slug: string) => go(routeForApp(slug));

  const openUserApp = (app: UserApp) => {
    const params = new URLSearchParams({
      workflow_id: app.workflow_id,
      app_id: app.id,
    });
    go(`/workflow?${params.toString()}`);
  };

  const submitUserApp = async (app: UserApp) => {
    setSubmittingAppId(app.id);
    try {
      const response = await apiPost<{ status: string; app?: UserApp }>(`/studio/user-apps/${app.id}/submit`);
      if (response.app) {
        setMyApps((current) => current.map((item) => (item.id === app.id ? { ...item, ...response.app } : item)));
      } else {
        setMyApps((current) =>
          current.map((item) =>
            item.id === app.id ? { ...item, status: "submitted", marketplace_status: "pending" } : item,
          ),
        );
      }
    } catch (err) {
      alert(err instanceof Error ? err.message : "Could not submit app for review.");
    } finally {
      setSubmittingAppId(null);
    }
  };

  const beginEditUserApp = (app: UserApp) => {
    setEditingAppId(app.id);
    setEditAppDraft({
      name: app.name,
      description: app.description || "",
      category: app.category || app.loop_type || "system",
      price_usd: app.price_usd ?? null,
    });
    setDeletingAppId(null);
  };

  const saveUserAppEdit = async (app: UserApp) => {
    const name = String(editAppDraft.name || "").trim();
    if (!name) {
      alert("App name is required.");
      return;
    }
    try {
      const response = await apiPatch<{ status: string; app: UserApp }>(`/studio/user-apps/${app.id}`, {
        name,
        description: String(editAppDraft.description || "").trim(),
        category: editAppDraft.category || app.category || app.loop_type || "system",
        price_usd: editAppDraft.price_usd ?? null,
      });
      setMyApps((current) => current.map((item) => (item.id === app.id ? { ...item, ...response.app } : item)));
      setEditingAppId(null);
      setEditAppDraft({});
    } catch (err) {
      alert(err instanceof Error ? err.message : "Could not update app.");
    }
  };

  const deleteUserApp = async (app: UserApp) => {
    setDeletingAppId(app.id);
    try {
      await apiDelete(`/studio/user-apps/${app.id}`);
      setMyApps((current) => current.filter((item) => item.id !== app.id));
      if (editingAppId === app.id) {
        setEditingAppId(null);
        setEditAppDraft({});
      }
    } catch (err) {
      alert(err instanceof Error ? err.message : "Could not delete app.");
    } finally {
      setDeletingAppId(null);
    }
  };

  async function skipOnboarding() {
    setOnboardingBusy(true);
    try {
      await apiPost("/settings/onboarding", { action: "skip", last_step: "skipped_from_apps" });
    } finally {
      setOnboardingComplete(true);
      setOnboardingBusy(false);
    }
  }


  

  const routeForApp = (slug: string) => {
    // Dedicated pages for apps with custom UX.

    const dedicated: Record<string, string> = {
      // Validation (dedicated pages)
      "validation-run": "/apps/validation-run",
      "validation-plan": "/apps/validation-plan",
      "bench-setup": "/apps/bench-setup",
      "preflight": "/apps/preflight",
      "validation-insights": "/apps/validation-insights",
    
      // Digital (dedicated pages)
      "arch2rtl": "/apps/arch2rtl",
      "arch2synthesis": "/apps/arch2synthesis",
      "arch2tapeout": "/apps/arch2tapeout",
      "rtl-review": "/apps/rtl-review",
      "constraint-review": "/apps/constraint-review",
      "timing-debug": "/apps/timing-debug",
      "fpga2rtl": "/apps/fpga2rtl",
      "fpga-bitstream": "/apps/fpga-bitstream",
      "integrate": "/apps/integrate",
      "dqa": "/apps/dqa",
      "verify": "/apps/verify",
      "smoke": "/apps/smoke",

      // Analog
      "analog-run": "/apps/analog-run",
      "analog-spec": "/apps/analog-spec",
      "analog-netlist": "/apps/analog-netlist",
      "analog-model": "/apps/analog-model",
      "analog-validate-model": "/apps/analog-validate-model",
      "analog-correlate": "/apps/analog-correlate",
      "analog-iterate": "/apps/analog-iterate",
      "analog-abstracts": "/apps/analog-abstracts",

      // Embedded
      "embedded-hal": "/apps/embedded-hal",
      "embedded-driver": "/apps/embedded-driver",
      "embedded-boot": "/apps/embedded-boot",
      "embedded-diagnostics": "/apps/embedded-diagnostics",
      "embedded-log-analyzer": "/apps/embedded-log-analyzer",
      "embedded-validate": "/apps/embedded-validate",
      "embedded-run": "/apps/embedded-run",

      // System
      "ask-project": "/apps/ask-project",
      "system-end2end": "/apps/system-end2end",
      "system-architecture": "/apps/system-architecture",
      "architecture-to-rtl": "/apps/architecture-to-rtl",
      "system-cache-tuning": "/apps/system-cache-tuning",
      "system-isa-compare": "/apps/system-isa-compare",
      "system-memory-bottleneck": "/apps/system-memory-bottleneck",
      "system-cpu-model": "/apps/system-cpu-model",
      "system-sim": "/apps/system-sim",
      "system-verify": "/apps/system-sim",
      "system-synthesis": "/apps/system-synthesis",
      "system-pd": "/apps/system-pd",
      "system-firmware": "/apps/system-firmware",
      "system-software": "/apps/system-software",
      "system-software-validation": "/apps/system-software-validation",
      "system-rtl": "/apps/system-rtl",
      "system-product-builder": "/apps/system-product-builder",
    };
    
    return dedicated[slug] || `/apps/${slug}`;
  };

  const referenceJourneys: ReferenceJourney[] = [
    {
      key: "temperature-monitor",
      exploreTitle: "Explore Temperature Monitor",
      segment: "Mixed-Signal / Product SoC",
      title: "Temperature Monitor SoC: analog sensor, System RTL, Sim, Firmware, Software, Validation, Product App",
      copy: "A System-first journey using digital_spec, analog_spec, and soc_spec. It builds a temperature sensor ADC behavioral model, digital threshold/alert RTL, integrated SoC top, system simulation, firmware/software, validation, and dashboard.",
      button: "Start System Temp Monitor Journey",
      onClick: startTempMonitorSystemDemo,
      stages: ["System RTL", "System Sim", "Firmware", "Software", "Validation", "Product App"],
    },
    {
      key: "pwm-controller",
      exploreTitle: "Explore PWM",
      segment: "Embedded Control / Motor & Power",
      title: "PWM Controller: RTL to Firmware to Software to Product App",
      copy: "A compact peripheral demo for first-time walkthroughs. Generated RTL, simulation, firmware co-simulation, and validation evidence come from actual workflow runs.",
      button: "Start PWM Reference Journey",
      onClick: startPwmFullStackDemo,
    },
    {
      key: "uart-packet-engine",
      exploreTitle: "Explore UART",
      segment: "Connectivity / Communications IP",
      title: "UART Packet Engine: FIFO, interrupts, firmware, software, and product app",
      copy: "A larger peripheral demo intended to produce roughly 150-200 flip-flops through FIFOs, shifters, counters, state machines, and interrupt logic.",
      button: "Start UART Reference Journey",
      onClick: startUartPacketDemo,
    },
    {
      key: "image-dma",
      exploreTitle: "Explore Image DMA",
      segment: "Vision / Edge AI Preprocessing",
      title: "Image DMA Pipeline: 25k FF visual processing demo",
      copy: "A large visual demo with DMA, register-based line buffers, 3x3 filtering, thresholding, histogram, interrupts, firmware, software, and product dashboard.",
      button: "Start Image DMA Journey",
      onClick: startImageDmaDemo,
    },
    {
      key: "sram-mbist",
      exploreTitle: "Explore SRAM MBIST",
      segment: "Memory / DFT",
      title: "SRAM MBIST Demo: Sky130 SRAM macro, scan, ATPG, and MBIST evidence",
      copy: "A focused memory-test journey using a 32x256 Sky130 SRAM scratchpad controller. Run Arch2RTL, then Arch2Synthesis to see scan DFT, ATPG readiness, and MBIST applicability evidence.",
      button: "Start MBIST SRAM Journey",
      onClick: startMbistSramDemo,
    },
    {
      key: "sensor-hub",
      exploreTitle: "Explore Sensor Hub",
      segment: "IoT / Embedded Edge Devices",
      title: "Smart Sensor Hub MCU: telemetry, alerts, low power, and product app",
      copy: "An IoT edge-node demo with a microcontroller-style sensor hub, threshold alerts, FIFO telemetry buffering, low-power sampling, firmware, software, validation, and dashboard.",
      button: "Start Sensor Hub Journey",
      onClick: startSensorHubDemo,
    },
    {
      key: "secure-boot",
      exploreTitle: "Explore Secure Boot",
      segment: "Security / Root-of-Trust IP",
      title: "Secure Boot + Key Manager: authentication, rollback, debug lock",
      copy: "A security reference journey with secure boot policy, key-slot selection, anti-rollback checks, tamper handling, firmware provisioning, validation, and dashboard.",
      button: "Start Secure Boot Journey",
      onClick: startSecureBootDemo,
    },
    {
      key: "safety-fault",
      exploreTitle: "Explore Safety Fault Manager",
      segment: "Automotive / Safety Control",
      title: "Safety Fault Manager + Watchdog: faults, heartbeat, reset escalation",
      copy: "A safety reference journey with watchdog timeout, heartbeat service, fault masks, escalation policy, reset request, firmware diagnostics, validation, and dashboard.",
      button: "Start Safety Journey",
      onClick: startSafetyFaultDemo,
    },
    {
      key: "fpga-prototype",
      exploreTitle: "Explore FPGA Prototype",
      segment: "FPGA / Board Bring-up",
      title: "PWM RTL to iCE40 Bitstream: generate, constrain, synthesize, place, route, time, and package",
      copy: "A board-oriented reference journey for proving a PWM RTL block on FPGA hardware before moving deeper into ASIC implementation. Start from predefined PWM RTL and iCEBreaker constraints, then generate synthesis, place-and-route, timing, and bitstream handoff evidence.",
      button: "Start PWM FPGA Journey",
      onClick: startPwmFpgaPrototypeDemo,
      stages: ["PWM RTL", "Board Constraints", "Yosys Synthesis", "nextpnr P&R", "Timing Check", "Bitstream"],
    },
  ];

  const catalogButtons: Array<{ view: CatalogView; title: string; body: string; count?: number }> = [
    { view: "digital", title: "Explore Digital apps", body: "RTL, DQA, verify, synthesis, tapeout, and handoff apps.", count: apps.filter((app) => app.loop_type === "digital").length },
    { view: "fpga", title: "Explore FPGA apps", body: "RTL handoff, iCE40 synthesis, place-and-route, timing, and bitstream handoff.", count: apps.filter((app) => app.loop_type === "fpga").length },
    { view: "system", title: "Explore System apps", body: "System RTL, simulation, synthesis, PD, firmware, software, validation, and product builder.", count: apps.filter((app) => app.loop_type === "system").length },
    { view: "analog", title: "Explore Analog apps", body: "Analog spec, netlist, model, validation, correlation, iteration, and abstracts.", count: apps.filter((app) => app.loop_type === "analog").length },
    { view: "embedded", title: "Explore Embedded apps", body: "HAL, drivers, boot, diagnostics, log analysis, co-sim, and firmware run.", count: apps.filter((app) => app.loop_type === "embedded").length },
    { view: "validation", title: "Explore Validation apps", body: "Validation plans, bench setup, preflight, execution orchestration, analytics, and insights.", count: apps.filter((app) => app.loop_type === "validation").length },
  ];

  const selectedCatalogLoop = ["digital", "fpga", "system", "analog", "embedded", "validation"].includes(catalogView)
    ? catalogView as LoopType
    : null;

  const selectedReference = referenceJourneys.find((journey) => journey.key === selectedReferenceJourney) || null;

  const loopForUserApp = (app: UserApp): LoopType => {
    const raw = String(app.loop_type || app.category || "system").toLowerCase();
    return LOOP_TYPES.includes(raw as LoopType) ? (raw as LoopType) : "system";
  };

  const openCatalog = (nextView: CatalogView) => {
    setCatalogView(nextView);
    window.setTimeout(() => {
      document.getElementById("apps-catalog-content")?.scrollIntoView({ behavior: "smooth", block: "start" });
    }, 0);
  };

  if (!onboardingLoading && !onboardingComplete) {
    return (
      <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
        <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
          <div className="mx-auto flex max-w-[1440px] items-center justify-between px-6 py-4">
            <button className="flex items-center gap-2 text-xl font-extrabold" onClick={() => go("/apps")}>
              <span className="text-cyan-400">ChipLoop</span>
              <span className="text-slate-400">/</span>
              <span className="text-slate-200">First Run</span>
            </button>
            <button
              onClick={skipOnboarding}
              disabled={onboardingBusy}
              className="rounded-xl border border-slate-700 px-4 py-2 text-slate-300 hover:bg-slate-900 disabled:opacity-60"
            >
              Skip for now
            </button>
          </div>
        </div>

        <section className="mx-auto grid max-w-[1440px] gap-6 px-6 py-10 lg:grid-cols-[1.05fr_0.95fr]">
          <div className="rounded-2xl border border-cyan-900/50 bg-slate-900/40 p-7 shadow-2xl">
            <div className="text-xs font-semibold uppercase text-cyan-300">Welcome to ChipLoop</div>
            <h1 className="mt-3 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">
              Complete your first chip workflow in a few minutes.
            </h1>
            <p className="mt-4 max-w-2xl text-slate-300">
              We will run a guided Arch2RTL demo using a simple PWM controller spec. Demo mode does not require trial checkout. You can run this demo up to 3 times, then start a 3-day trial when you are ready to use your own specs.
            </p>

            <div className="mt-6 grid gap-3 sm:grid-cols-3">
              {[
                ["1", "Review the spec", "A simple PWM design is pre-filled."],
                ["2", "Run Arch2RTL", "Watch the workflow produce artifacts."],
                ["3", "Inspect and download", "Open RTL, SDC, UPF, then download ZIP."],
              ].map(([step, title, copy]) => (
                <div key={step} className="rounded-xl border border-slate-800 bg-black/30 p-4">
                  <div className="flex h-8 w-8 items-center justify-center rounded-full bg-cyan-600 text-sm font-bold">{step}</div>
                  <div className="mt-3 font-semibold text-slate-100">{title}</div>
                  <div className="mt-1 text-sm text-slate-400">{copy}</div>
                </div>
              ))}
            </div>

            <div className="mt-7 flex flex-wrap gap-3">
              <button
                onClick={startArch2RtlOnboarding}
                disabled={onboardingBusy}
                className="rounded-xl bg-cyan-600 px-6 py-3 font-bold text-white hover:bg-cyan-500 disabled:opacity-60"
              >
                {onboardingBusy ? "Starting..." : "Start Arch2RTL Demo"}
              </button>
              <button
                onClick={skipOnboarding}
                disabled={onboardingBusy}
                className="rounded-xl border border-slate-700 bg-slate-950/40 px-6 py-3 font-semibold text-slate-200 hover:bg-slate-950 disabled:opacity-60"
              >
                Go to Apps
              </button>
            </div>
          </div>

          <div className="rounded-2xl border border-slate-800 bg-black/35 p-6">
            <div className="text-sm font-semibold text-slate-300">Demo spec preview</div>
            <pre className="mt-4 max-h-[460px] overflow-auto whitespace-pre-wrap rounded-xl border border-slate-800 bg-slate-950 p-4 text-sm leading-6 text-slate-200">
              {ARCH2RTL_ONBOARDING_SPEC}
            </pre>
            <div className="mt-4 rounded-xl border border-emerald-900/50 bg-emerald-950/20 p-4 text-sm text-emerald-100">
              You only need to click run, review the generated files, and download the package. After each demo run, ChipLoop will offer a 3-day trial for custom specs without blocking until the demo limit is used.
            </div>
          </div>
        </section>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="apps" showPlanBadge />
      <LowCreditBanner />

      {/* Hero */}
      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-6 pb-6 pt-10">
        <div className="mx-auto max-w-[1440px] rounded-2xl border border-slate-800 bg-slate-950/55 p-6 shadow-lg">
          <div className="flex items-start justify-between gap-4">
            <div>
              <div className="text-xs text-slate-400">
                Welcome{userEmail ? `, ${userEmail}` : ""} | <span className="text-slate-200">Start here</span>
              </div>
              <h1 className="mt-2 text-4xl font-extrabold leading-tight text-white sm:text-5xl">
                Run outcomes, not workflows.
              </h1>
              <p className="mt-2 max-w-xl text-slate-300">
                Pick an app, give inputs once, click run. ChipLoop handles execution, learning, and reporting.
              </p>
            </div>

            <span className="shrink-0 rounded-full border border-slate-700 bg-slate-900 px-3 py-1 text-xs text-slate-200">
              Recommended
            </span>
          </div>

          <div className="mt-6">
            <div className="text-xs font-semibold uppercase text-cyan-300">What would you like to do today?</div>
            <button
              onClick={() => openApp("ask-project")}
              className="mt-4 w-full rounded-2xl border border-slate-800 bg-slate-900/70 p-5 text-left transition hover:border-cyan-400 hover:bg-slate-900"
            >
              <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
                <div>
                  <div className="text-xs font-semibold uppercase text-cyan-300">Project review</div>
                  <div className="mt-2 text-xl font-bold text-white">Ask this Project</div>
                  <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                    Upload files, paste content, or import selected GitHub repo files. Ask for summaries, risks, suggestions, and the next ChipLoop workflow to run.
                  </p>
                </div>
                <span className="shrink-0 rounded-full border border-slate-700 bg-slate-950 px-3 py-1 text-xs font-semibold text-slate-200">
                  New
                </span>
              </div>
            </button>
            <div className="mt-2 text-lg font-bold">Flagship apps</div>
            <div className="text-sm text-slate-400">Best starting points before choosing a category.</div>
          </div>

          <div className="mt-5 grid gap-4 md:grid-cols-2">
            {featuredApps.map((featured) => (
              <button
                key={featured.slug}
                onClick={() => openApp(featured.slug)}
                className="rounded-2xl border border-slate-800 bg-black/30 p-5 text-left transition hover:border-cyan-700 hover:bg-slate-950"
              >
                <div className="flex items-center justify-between gap-3">
                  <div className="text-xl font-bold text-white">{featured.title}</div>
                  <span className="rounded-full border border-slate-700 bg-slate-900 px-2 py-1 text-xs text-slate-200">
                    {featured.nudge || "Recommended"}
                  </span>
                </div>
                <div className="mt-2 min-h-[48px] text-slate-300">{featured.subtitle}</div>
                {featured.promise ? (
                  <div className="mt-3 text-sm text-slate-400">
                    Outcome: <span className="text-slate-200">{featured.promise}</span>
                  </div>
                ) : null}
                <div className="mt-4 text-xs text-slate-500">
                  Progressive outputs | Executive summary | ZIP artifacts
                </div>
              </button>
            ))}
          </div>
        </div>
      </section>

      {(myAppsLoading || myApps.length > 0) ? (
        <section className="mx-auto max-w-[1440px] px-6 pb-7">
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-6">
            <div className="flex flex-col gap-3 sm:flex-row sm:items-end sm:justify-between">
              <div>
                <div className="text-xs font-semibold uppercase text-cyan-300">My Apps</div>
                <h2 className="mt-2 text-3xl font-extrabold leading-tight text-white sm:text-4xl">Private apps from Studio</h2>
                <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                  Apps created from your workflows stay private until submitted and approved for marketplace publication.
                </p>
              </div>
              <button
                onClick={() => go("/workflow")}
                className="rounded-xl border border-slate-600 px-5 py-3 text-sm font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200"
              >
                Create in Studio
              </button>
            </div>

            {myAppsLoading ? (
              <div className="mt-6 rounded-xl border border-slate-800 bg-slate-950/45 p-4 text-sm text-slate-400">
                Loading private apps...
              </div>
            ) : (
              <div className="mt-6 grid gap-4 md:grid-cols-2 lg:grid-cols-3">
                {myApps.map((app) => {
                  const loopKey = loopForUserApp(app);
                  const meta = LOOP_META[loopKey];
                  const editing = editingAppId === app.id;
                  return (
                    <div
                      key={app.id}
                      className={`rounded-2xl border ${meta.border} bg-slate-950/55 p-4 text-left transition hover:bg-slate-950`}
                    >
                      <div className="flex items-center justify-between gap-2">
                        <div className="flex min-w-0 items-center gap-3">
                          <div className={`flex h-9 w-9 shrink-0 items-center justify-center rounded-xl border ${meta.border} ${meta.softBg} text-sm font-bold`}>
                            {meta.icon}
                          </div>
                          <div className="truncate text-lg font-bold text-slate-100">{app.name}</div>
                        </div>
                        <span className="rounded-full border border-slate-700 bg-slate-900/40 px-2 py-1 text-xs text-slate-200">
                          {app.visibility || "private"}
                        </span>
                      </div>
                      <div className="mt-3 min-h-10 text-sm leading-5 text-slate-300">
                          {app.description || `Workflow app from ${app.workflow_name || "Studio"}.`}
                      </div>
                      {editing ? (
                        <div className="mt-4 grid gap-3 rounded-xl border border-slate-800 bg-black/25 p-3">
                          <input
                            value={String(editAppDraft.name || "")}
                            onChange={(event) => setEditAppDraft((current) => ({ ...current, name: event.target.value }))}
                            className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                            placeholder="App name"
                          />
                          <textarea
                            value={String(editAppDraft.description || "")}
                            onChange={(event) => setEditAppDraft((current) => ({ ...current, description: event.target.value }))}
                            rows={3}
                            className="resize-none rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                            placeholder="Description"
                          />
                          <div className="grid gap-3 sm:grid-cols-2">
                            <select
                              value={String(editAppDraft.category || loopKey)}
                              onChange={(event) => setEditAppDraft((current) => ({ ...current, category: event.target.value }))}
                              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                            >
                              {LOOP_TYPES.map((item) => <option key={item} value={item}>{LOOP_META[item].title}</option>)}
                            </select>
                            <input
                              value={editAppDraft.price_usd == null ? "" : String(editAppDraft.price_usd)}
                              onChange={(event) => setEditAppDraft((current) => ({ ...current, price_usd: event.target.value ? Number(event.target.value) : null }))}
                              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                              placeholder="Price USD"
                            />
                          </div>
                        </div>
                      ) : null}
                      <div className="mt-4 space-y-2 rounded-xl border border-slate-800 bg-black/20 p-3 text-xs text-slate-400">
                        <div>
                          Workflow: <span className="text-slate-200">{app.workflow_name || app.workflow_id}</span>
                        </div>
                        <div>
                          Marketplace: <span className="text-slate-200">{app.marketplace_status || "draft"}</span>
                        </div>
                      </div>
                      <div className="mt-4 flex flex-wrap gap-2">
                        {editing ? (
                          <>
                            <button
                              onClick={() => saveUserAppEdit(app)}
                              className="rounded-lg bg-cyan-500 px-3 py-2 text-xs font-bold text-black transition hover:bg-cyan-400"
                            >
                              Save
                            </button>
                            <button
                              onClick={() => {
                                setEditingAppId(null);
                                setEditAppDraft({});
                              }}
                              className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-bold text-slate-200 transition hover:border-cyan-400 hover:text-cyan-200"
                            >
                              Cancel
                            </button>
                          </>
                        ) : (
                          <button
                            onClick={() => beginEditUserApp(app)}
                            className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-bold text-slate-200 transition hover:border-cyan-400 hover:text-cyan-200"
                          >
                            Edit
                          </button>
                        )}
                        <button
                          onClick={() => openUserApp(app)}
                          className="rounded-lg bg-cyan-500 px-3 py-2 text-xs font-bold text-black transition hover:bg-cyan-400"
                        >
                          Open in Studio
                        </button>
                        <button
                          onClick={() => submitUserApp(app)}
                          disabled={submittingAppId === app.id || app.marketplace_status === "pending" || app.status === "submitted"}
                          className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-bold text-slate-200 transition hover:border-cyan-400 hover:text-cyan-200 disabled:cursor-not-allowed disabled:border-slate-800 disabled:text-slate-600"
                        >
                          {app.marketplace_status === "pending" || app.status === "submitted"
                            ? "Submitted"
                            : submittingAppId === app.id
                            ? "Submitting..."
                            : "Submit for Review"}
                        </button>
                        <button
                          onClick={() => deleteUserApp(app)}
                          disabled={deletingAppId === app.id}
                          className="rounded-lg border border-rose-700 px-3 py-2 text-xs font-bold text-rose-100 transition hover:bg-rose-950/30 disabled:cursor-not-allowed disabled:border-slate-800 disabled:text-slate-600"
                        >
                          {deletingAppId === app.id ? "Deleting..." : "Delete"}
                        </button>
                      </div>
                    </div>
                  );
                })}
              </div>
            )}
          </div>
        </section>
      ) : null}

      <section id="reference-journeys" className="mx-auto max-w-[1440px] px-6 pb-7 scroll-mt-24">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-6">
          <div className="flex flex-col gap-3 sm:flex-row sm:items-end sm:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase text-cyan-300">Experience Apps</div>
              <h2 className="mt-2 text-3xl font-extrabold leading-tight text-white sm:text-4xl">Choose one catalog view</h2>
              <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                Open a focused page for one app family without scrolling through every app at once.
              </p>
            </div>
            {catalogView !== "home" ? (
              <button
                onClick={() => openCatalog("home")}
                className="rounded-xl border border-slate-600 px-5 py-3 text-sm font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200"
              >
                Back to overview
              </button>
            ) : null}
          </div>
          <div className="mt-6 grid gap-4 md:grid-cols-2 lg:grid-cols-3">
            {catalogButtons.map((item) => {
              const active = catalogView === item.view;
              return (
                <button
                  key={item.view}
                  onClick={() => openCatalog(item.view)}
                  className={`min-h-[132px] rounded-xl px-5 py-4 text-left transition ${
                    active
                      ? "bg-cyan-400 text-slate-950 shadow-lg shadow-cyan-950/30 hover:bg-cyan-300"
                      : "border border-slate-600 bg-slate-950/35 text-white hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  <div className="flex items-start justify-between gap-3">
                    <div className="text-lg font-extrabold">{item.title}</div>
                    {item.count !== undefined ? (
                      <span className={`rounded-full px-2 py-1 text-xs font-bold ${active ? "bg-slate-950/10 text-slate-900" : "border border-slate-700 text-slate-300"}`}>
                        {item.count}
                      </span>
                    ) : null}
                  </div>
                  <div className={`mt-3 text-sm font-semibold leading-6 ${active ? "text-slate-900" : "text-slate-300"}`}>
                    {item.body}
                  </div>
                </button>
              );
            })}
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-[1440px] px-6 pb-7">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-6">
          <div className="flex flex-col gap-3 sm:flex-row sm:items-end sm:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase text-cyan-300">Experience Reference Journeys</div>
              <h2 className="mt-2 text-3xl font-extrabold leading-tight text-white sm:text-4xl">Choose one guided product journey</h2>
              <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                Start an end-to-end reference flow using the standard ChipLoop apps, stage sequence, and demo collateral.
              </p>
            </div>
            {selectedReference ? (
              <button
                onClick={() => setSelectedReferenceJourney(null)}
                className="rounded-xl border border-slate-600 px-5 py-3 text-sm font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200"
              >
                Clear journey
              </button>
            ) : null}
          </div>
          <div className="mt-6 grid gap-4 md:grid-cols-2 lg:grid-cols-4">
            {referenceJourneys.map((journey) => {
              const active = selectedReferenceJourney === journey.key;
              return (
                <button
                  key={journey.key}
                  onClick={() => {
                    setSelectedReferenceJourney(journey.key);
                    window.setTimeout(() => {
                      document.getElementById("reference-journey-detail")?.scrollIntoView({ behavior: "smooth", block: "start" });
                    }, 0);
                  }}
                  className={`min-h-[132px] rounded-xl px-5 py-4 text-left transition ${
                    active
                      ? "bg-cyan-400 text-slate-950 shadow-lg shadow-cyan-950/30 hover:bg-cyan-300"
                      : "border border-slate-600 bg-slate-950/35 text-white hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  <div className="text-lg font-extrabold">{journey.exploreTitle}</div>
                  <div className={`mt-3 text-sm font-semibold leading-6 ${active ? "text-slate-900" : "text-slate-300"}`}>
                    {journey.segment}
                  </div>
                </button>
              );
            })}
          </div>
        </div>
      </section>

      {selectedReference ? (
        <section id="reference-journey-detail" className="mx-auto max-w-[1440px] px-6 pb-7 scroll-mt-24">
          <div className="rounded-2xl border border-slate-800 bg-slate-950/45 p-5">
            <div className="mb-2 text-xs font-semibold uppercase text-cyan-300">{selectedReference.segment}</div>
            <div className="text-xl font-bold text-white">{selectedReference.title}</div>
            <p className="mt-2 text-sm leading-6 text-slate-300">{selectedReference.copy}</p>
            <div className="mt-4 flex flex-wrap items-center gap-2 text-xs text-slate-300">
              {(selectedReference.stages || ["Arch2RTL", "Verify", "Firmware", "Software", "Validation", "Product App"]).map((stage, index, stages) => (
                <div key={stage} className="flex items-center gap-2">
                  <span className="rounded border border-slate-700 bg-slate-900 px-2 py-1">{stage}</span>
                  {index < stages.length - 1 ? <span className="text-slate-500">&gt;</span> : null}
                </div>
              ))}
            </div>
            <button
              onClick={selectedReference.onClick}
              className="mt-5 rounded-xl bg-cyan-600 px-5 py-3 font-semibold text-white transition hover:bg-cyan-500"
            >
              {selectedReference.button}
            </button>
          </div>
        </section>
      ) : null}

      {/* Loop rows */}
      {selectedCatalogLoop ? (
      <section id="apps-catalog-content" className="mx-auto max-w-[1440px] px-6 pb-16 space-y-10 scroll-mt-24">
        {[selectedCatalogLoop].map((loop) => {
          const meta = LOOP_META[loop];
          const rowApps = apps.filter((a) => a.loop_type === loop);

          return (
            <div key={loop}>
              <div className="mb-3 flex items-end justify-between">
                <div>
                  <div className="flex items-center gap-2">
                    <div className={`h-2 w-2 rounded-full ${meta.accent}`} />
                    <div className="text-xl font-bold">{meta.title}</div>
                  </div>
                  <div className="text-sm text-slate-400">{meta.tagline}</div>
                </div>

                <button onClick={() => setCatalogView("home")} className="text-sm text-cyan-300 hover:underline">
                  Back to overview
                </button>
              </div>

              <div className="grid gap-4 md:grid-cols-3">
                  {rowApps.map((app) => (
                    <button
                      key={app.slug}
                      onClick={() => openApp(app.slug)}
                      className={`rounded-2xl border ${meta.border} bg-slate-950/55 p-4 text-left hover:bg-slate-950 transition`}
                    >
                      <div className="flex items-center justify-between gap-2">
                        <div className="flex min-w-0 items-center gap-3">
                          <div className={`flex h-9 w-9 shrink-0 items-center justify-center rounded-xl border ${meta.border} ${meta.softBg} text-sm font-bold`}>
                            {meta.icon}
                          </div>
                          <div className="truncate text-lg font-bold text-slate-100">{app.title}</div>
                        </div>
                        {app.status ? (
                          <span className="rounded-full border border-slate-700 bg-slate-900/40 px-2 py-1 text-xs text-slate-200">
                            {app.status}
                          </span>
                        ) : null}
                      </div>

                      <div className="mt-3 min-h-10 text-sm leading-5 text-slate-300">{app.subtitle}</div>

                      <div className="mt-4 space-y-2 rounded-xl border border-slate-800 bg-black/20 p-3 text-xs text-slate-400">
                        <div>
                          Input: <span className="text-slate-200">{outcomeInputs[app.loop_type]}</span>
                        </div>
                        <div>
                          Output: <span className="text-slate-200">{app.promise || outcomeOutputs[app.loop_type]}</span>
                        </div>
                      </div>

                      <div className="mt-3 flex items-center justify-between">
                        {app.nudge ? (
                          <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                            {app.nudge}
                          </span>
                        ) : <span />}

                        <span className="text-xs text-slate-500">Open</span>
                      </div>
                    </button>
                  ))}
              </div>
            </div>
          );
        })}
      </section>
      ) : null}
    </main>
  );
}










