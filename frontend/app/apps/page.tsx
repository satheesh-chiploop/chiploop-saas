// âœ… AFTER: app_apps_page.tsx (minimal edits only)

"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";
import { apiGet, apiPost } from "@/lib/apiClient";
import { LowCreditBanner, PlanCreditBadge } from "@/components/PlanCreditStatus";

const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

type LoopType = "digital" | "validation" | "analog" | "embedded" | "system";

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
  status?: "Flagship" | "Coming";
  nudge?: "Recommended" | "Most used" | "New";
  promise?: string;
};

const LOOP_META: Record<LoopType, { title: string; tagline: string; accent: string }> = {
  digital: { title: "Digital Loop", tagline: "Design â†’ RTL â†’ Verify â†’ Improve", accent: "accent-digital" },
  validation: { title: "Validation Loop", tagline: "Plan â†’ Run â†’ Learn â†’ Improve", accent: "accent-validation" },
  analog: { title: "Analog Loop", tagline: "Analyze â†’ Simulate â†’ Correlate â†’ Improve", accent: "accent-analog" },
  embedded: { title: "Embedded(Firmware) Loop", tagline: "Code â†’ Run â†’ Observe â†’ Fix", accent: "accent-embedded" },
  system: { title: "System Loop", tagline: "Integrate â†’ Analyze â†’ Optimize", accent: "accent-system" },
};

export default function AppsHomePage() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);
  const [onboardingLoading, setOnboardingLoading] = useState(true);
  const [onboardingComplete, setOnboardingComplete] = useState(true);
  const [onboardingBusy, setOnboardingBusy] = useState(false);

  const [view, setView] = useState<"recommended" | "all">("recommended");

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

  // âœ… updated apps list (only change is digital apps)
  const apps: AppCard[] = useMemo(() => ([
    {
      slug: "validation-run",
      title: "Validation Run",
      subtitle: "One-click run on real hardware with preflight + learning",
      loop_type: "validation",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Get run results + gaps + exec report",
    },

    // âœ… NEW DIGITAL FLAGSHIPS
    {
      slug: "arch2rtl",
      title: "Arch2RTL",
      subtitle: "Spec â†’ Architecture â†’ Microarch â†’ RTL â†’ Handoff package",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Most used",
      promise: "Generate RTL + docs + handoff artifacts",
    },
    {
      slug: "arch2synthesis",
      title: "Arch2Synthesis",
      subtitle: "Arch2RTL + Synthesis (or RTL â†’ Synthesis) with reports",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Fast path",
      promise: "Get clean netlist + timing/area/power reports",
    },
    
    {
      slug: "arch2tapeout",
      title: "Arch2Tapeout",
      subtitle: "Arch2RTL + Synthesis + RTLâ†’GDS pipeline (partial runs supported)",
      loop_type: "digital",
      status: "Flagship",
      nudge: "End-to-end",
      promise: "Run RTLâ†’GDS with DRC/LVS/Tapeout + exec summary",
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
      subtitle: "Text â†’ Integration intent â†’ Top RTL + report",
      loop_type: "digital",
      status: "Flagship",
      nudge: "New",
      promise: "Assemble IPs into a runnable top",
    },

    {
      slug: "validation-plan",
      title: "Validation Plan & Coverage",
      subtitle: "Datasheet/spec â†’ test plan + coverage map + gaps",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Structured plan + coverage gaps in one shot",
    },
    {
      slug: "bench-setup",
      title: "Bench Setup",
      subtitle: "Register instruments â†’ create bench â†’ schematic â†’ preflight",
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
      subtitle: "Analyze past runs â†’ patterns â†’ evolve plan + coverage",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Turn history into next test improvements",
    },

    // âœ… NEW ANALOG APPS
    {
      slug: "analog-run",
      title: "Analog Run",
      subtitle: "Spec â†’ Netlist â†’ Model â†’ Validate â†’ Correlate â†’ Iterate",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Recommended",
      promise: "End-to-end analog loop",
    },
    {
      slug: "analog-spec",
      title: "Analog Spec",
      subtitle: "Text â†’ structured spec + open questions",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Most used",
      promise: "Clean spec JSON",
    },
    {
      slug: "analog-netlist",
      title: "Analog Netlist",
      subtitle: "Spec â†’ SPICE scaffold + sim plan",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "Netlist + sim plan",
    },
    {
      slug: "analog-model",
      title: "Analog Model",
      subtitle: "Spec â†’ SV RNM / Verilog-A behavioral model",
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

    // âœ… EMBEDDED (production firmware chain)
    {
      slug: "embedded-run",
      title: "Embedded Run",
      subtitle: "End-to-end firmware flow: HAL â†’ Drivers â†’ Boot â†’ Diagnostics â†’ Co-sim â†’ Report",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Production-ready firmware package + exec summary",
    },
    {
      slug: "embedded-hal",
      title: "Embedded HAL",
      subtitle: "Register extraction â†’ Rust HAL layer â†’ validation",
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
      subtitle: "Logs â†’ fault classification â†’ root cause â†’ fix plan",
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
    // âœ… SYSTEM (Tiny Sensor Hub SoC)
    {
      slug: "system-end2end",
      title: "System End2End",
      subtitle: "Digital + Analog + SoC integration â†’ Sim + PD + Firmware â†’ ZIP",
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
      slug: "system-pd",
      title: "System PD",
      subtitle: "SoC RTL2GDS with OpenLane2 pipeline (DRC/LVS/Tapeout)",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "GDS + DRC/LVS + exec summary",
    },
    {
      slug: "system-rtl",
      title: "System RTL",
      subtitle: "Digital + Analog + SoC intent â†’ integrated top RTL + handoff package",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Generate integrated system RTL + top assembly artifacts",
    },
    {
      slug: "system-firmware",
      title: "System Firmware",
      subtitle: "Register extract â†’ driver scaffold â†’ build â†’ co-sim results",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Firmware drivers + co-sim report",
    },
    {
      slug: "system-software",
      title: "System Software",
      subtitle: "Firmware handoff â†’ SDK â†’ API â†’ applications",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Generate SDK + APIs + software package",
    },
    {
      slug: "system-software-validation",
      title: "System Software Validation",
      subtitle: "Validate software package or run full software â†’ firmware â†’ RTL co-simulation",
      loop_type: "system",
      status: "Flagship",
      nudge: "New",
      promise: "Build + test + contract + package validation or full co-sim proof",
    },

  ]), []);

  const featured = apps.find(a => a.slug === "arch2tapeout") || apps[0];

  const FLAGSHIP_SLUGS = new Set<string>([
    // Validation (1â€“2)
    "validation-run",
    "validation-plan",

    // Digital (1â€“2)
    "arch2rtl",
    "arch2synthesis",
    "dqa",

    // Analog (1â€“2)
    "analog-run",
    "analog-model",

    // Embedded (1â€“2)
    "embedded-run",
    "embedded-driver",

    // System 
    "system-rtl",
    "system-firmware",
    "system-software",

  ]);

  const flagship = apps.filter(a => a.status === "Flagship" && FLAGSHIP_SLUGS.has(a.slug));

  const loops: LoopType[] = useMemo(() => (["digital", "analog", "embedded", "validation","system"]), []);

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
    // âœ… Dedicated pages (apps with custom UX)

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
      "integrate": "/apps/integrate",
      "dqa": "/apps/dqa",
      "verify": "/apps/verify",
      "smoke": "/apps/smoke",

      // âœ… ANALOG
      "analog-run": "/apps/analog-run",
      "analog-spec": "/apps/analog-spec",
      "analog-netlist": "/apps/analog-netlist",
      "analog-model": "/apps/analog-model",
      "analog-validate-model": "/apps/analog-validate-model",
      "analog-correlate": "/apps/analog-correlate",
      "analog-iterate": "/apps/analog-iterate",
      "analog-abstracts": "/apps/analog-abstracts",

      // âœ… EMBEDDED (dedicated pages)
      "embedded-hal": "/apps/embedded-hal",
      "embedded-driver": "/apps/embedded-driver",
      "embedded-boot": "/apps/embedded-boot",
      "embedded-diagnostics": "/apps/embedded-diagnostics",
      "embedded-log-analyzer": "/apps/embedded-log-analyzer",
      "embedded-validate": "/apps/embedded-validate",
      "embedded-run": "/apps/embedded-run",

      // âœ… SYSTEM (dedicated pages)
      "system-end2end": "/apps/system-end2end",
      "system-sim": "/apps/system-sim",
      "system-pd": "/apps/system-pd",
      "system-firmware": "/apps/system-firmware",
      "system-software": "/apps/system-software",
      "system-software-validation": "/apps/system-software-validation",
      "system-rtl": "/apps/system-rtl",
    };
    
    return dedicated[slug] || `/apps/${slug}`;
  };

  if (!onboardingLoading && !onboardingComplete) {
    return (
      <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
        <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
          <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
            <button className="flex items-center gap-2 text-xl font-extrabold" onClick={() => go("/apps")}>
              <span className="text-cyan-400">CHIPLOOP</span>
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

        <section className="mx-auto grid max-w-6xl gap-6 px-6 py-10 lg:grid-cols-[1.05fr_0.95fr]">
          <div className="rounded-2xl border border-cyan-900/50 bg-slate-900/40 p-7 shadow-2xl">
            <div className="text-sm font-semibold uppercase tracking-wide text-cyan-300">Welcome to ChipLoop</div>
            <h1 className="mt-3 text-4xl font-extrabold leading-tight text-white">
              Complete your first chip workflow in a few minutes.
            </h1>
            <p className="mt-4 max-w-2xl text-slate-300">
              We will run a guided Arch2RTL demo using a simple PWM controller spec. You will generate RTL, constraints, UPF-lite power intent, and a downloadable handoff package.
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
              You only need to click run, review the generated files, and download the package. Studio remains available after this for advanced customization.
            </div>
          </div>
        </section>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      {/* Top bar */}
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button
            className="flex items-center gap-2 text-xl font-extrabold"
            onClick={() => go("/")}
            title="Home"
          >
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">Apps</span>
          </button>

          <div className="flex items-center gap-3">
            <PlanCreditBadge />
            <button
              onClick={() => go("/")}
              className="rounded-xl border border-slate-700 px-4 py-2 text-slate-300 hover:bg-slate-900 transition"
            >
              Home
            </button>
            <button
              onClick={() => go("/workflow")}
              className="rounded-xl bg-slate-800 px-4 py-2 text-slate-200 hover:bg-slate-700 transition"
              title="Advanced Builder"
            >
              Studio
            </button>
            <button
              onClick={() => go("/settings/api-keys")}
              className="rounded-xl border border-slate-700 px-4 py-2 text-slate-300 hover:bg-slate-900 transition"
            >
              Settings
            </button>
            <button
              onClick={async () => {
                await supabase.auth.signOut();
                go("/");
              }}
              className="rounded-xl border border-slate-700 px-4 py-2 text-slate-300 hover:bg-slate-900 transition"
            >
              Logout
            </button>
          </div>
        </div>
      </div>
      <LowCreditBanner />

      {/* Hero */}
      <section className="mx-auto max-w-6xl px-6 pt-10 pb-6">
        <div className="grid gap-4 md:grid-cols-5">
          <div className="md:col-span-3 rounded-2xl border border-slate-800 bg-slate-900/30 p-6 shadow-lg">
            <div className="flex items-start justify-between gap-4">
              <div>
                <div className="text-xs text-slate-400">
                  Welcome{userEmail ? `, ${userEmail}` : ""} â€¢ <span className="text-cyan-300">Start here</span>
                </div>
                <h1 className="mt-2 text-3xl font-extrabold leading-tight">
                  Run outcomes, not workflows.
                </h1>
                <p className="mt-2 max-w-xl text-slate-300">
                  Pick an app, give inputs once, click run. ChipLoop handles execution, learning, and reporting.
                </p>
              </div>

              <span className="shrink-0 rounded-full border border-cyan-900/60 bg-cyan-500/10 px-3 py-1 text-xs text-cyan-200">
                Recommended
              </span>
            </div>

            <div className="mt-5 rounded-2xl border border-slate-800 bg-black/30 p-5">
              <div className="flex items-start justify-between gap-4">
                <div>
                  <div className="text-sm text-slate-400">Featured</div>
                  <div className="mt-1 text-2xl font-bold text-white">{featured.title}</div>
                  <div className="mt-1 text-slate-300">{featured.subtitle}</div>

                  <div className="mt-5 flex flex-wrap gap-3">
                    <button
                      onClick={() => go(routeForApp(featured.slug))}
                      className="rounded-xl bg-cyan-600 px-5 py-3 font-semibold hover:bg-cyan-500 transition"
                    >
                      Run now
                    </button>
                    <button
                      onClick={() => go(routeForApp(featured.slug))}
                      className="rounded-xl border border-slate-700 bg-slate-950/40 px-5 py-3 text-slate-200 hover:bg-slate-950 transition"
                    >
                      Preview outputs
                    </button>
                  </div>

                  <div className="mt-4 text-xs text-slate-500">
                    Progressive outputs â€¢ Executive summary â€¢ ZIP artifacts
                  </div>
                </div>
              </div>
            </div>
          </div>

          {/* Right */}
          <div className="md:col-span-2 rounded-2xl border border-slate-800 bg-slate-900/20 p-6">
            <div className="text-sm text-slate-400">Quick choices</div>
            <div className="mt-2 text-xl font-bold">What do you want to do today?</div>

            <div className="mt-4 space-y-3">
              <button
                onClick={() => go("/apps/validation-run")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Run validation on hardware</div>
                  <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                    Recommended
                  </span>
                </div>
                <div className="mt-1 text-sm text-slate-400">Bench â†’ instruments â†’ preflight â†’ run â†’ report</div>
              </button>

              {/* âœ… change this to Arch2RTL */}
              <button
                onClick={() => go("/apps/arch2rtl")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Digital - Spec â†’ RTL + handoff</div>
                  <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                    Most used
                  </span>
                </div>
                <div className="mt-1 text-sm text-slate-400"> Digital - Arch2RTL: docs + SV + package</div>
              </button>

              {/* âœ… NEW: Analog daily-use */}
              <button
                onClick={() => go("/apps/analog-run")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Run analog loop end-to-end</div>
                  <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                    Recommended
                  </span>
                </div>
                  <div className="mt-1 text-sm text-slate-400">Analog Run: netlist â†’ model â†’ validate â†’ correlate</div>
              </button>

              {/* âœ… NEW: Embedded daily-use */}
              <button
                onClick={() => go("/apps/embedded-run")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Run firmware loop end-to-end</div>
                  <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                    Recommended
                  </span>
                </div>
                  <div className="mt-1 text-sm text-slate-400">Embedded Run: HAL â†’ drivers â†’ boot â†’ diagnostics â†’ report</div>
              </button>
            </div>

            <button
              onClick={() => go("/apps/system-software-validation")}
              className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
            >
              <div className="flex items-center justify-between">
                <div className="font-semibold">Validate system software stack</div>
                <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                  New
                </span>
              </div>
              <div className="mt-1 text-sm text-slate-400">
                Software validation or full co-simulation (SW â†’ FW â†’ RTL)
              </div>
            </button>



            <div className="mt-6 flex items-center gap-2">
              <button
                onClick={() => setView("recommended")}
                className={`rounded-xl px-4 py-2 text-sm border transition ${
                  view === "recommended"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                }`}
              >
                Recommended
              </button>
              <button
                onClick={() => setView("all")}
                className={`rounded-xl px-4 py-2 text-sm border transition ${
                  view === "all"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                }`}
              >
                Explore all loops
              </button>
            </div>
          </div>
        </div>
      </section>

      {/* Flagship row */}
      <section className="mx-auto max-w-6xl px-6 pb-4">
        <div className="mb-3 flex items-end justify-between">
          <div>
            <div className="text-lg font-bold">Flagship apps</div>
            <div className="text-sm text-slate-400">Best starting points.</div>
          </div>
        </div>

        <div className="grid gap-4 md:grid-cols-2">
          {flagship.map((app) => (
            <button
              key={app.slug}
              onClick={() => go(routeForApp(app.slug))}
              className="rounded-2xl border border-slate-800 bg-slate-950/50 p-5 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
            >
              <div className="flex items-center justify-between gap-3">
                <div className="text-xl font-bold">{app.title}</div>
                <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                  {app.nudge || "Flagship"}
                </span>
              </div>
              <div className="mt-2 text-slate-300">{app.subtitle}</div>
              {app.promise ? (
                <div className="mt-3 text-sm text-slate-400">
                  Outcome: <span className="text-slate-200">{app.promise}</span>
                </div>
              ) : null}
              <div className="mt-4 text-xs text-slate-500">One click â†’ progressive outputs â†’ ZIP</div>
            </button>
          ))}
        </div>
      </section>

      {/* Loop rows */}
      <section className="mx-auto max-w-6xl px-6 pb-16 space-y-10">
        {(view === "recommended" ? loops.filter(l => l === "digital" || l === "analog" || l === "embedded" || l === "validation" || l === "system") : loops).map((loop) => {
          const meta = LOOP_META[loop];
          const rowApps = apps.filter((a) => a.loop_type === loop);
          const animatedApps = [...rowApps, ...rowApps, ...rowApps];

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

                <button onClick={() => setView("all")} className="text-sm text-cyan-300 hover:underline">
                  See all
                </button>
              </div>

              <div className="relative overflow-hidden rounded-2xl border border-slate-800 bg-slate-900/15">
                <div className="pointer-events-none absolute inset-y-0 left-0 w-16 bg-gradient-to-r from-black to-transparent" />
                <div className="pointer-events-none absolute inset-y-0 right-0 w-16 bg-gradient-to-l from-black to-transparent" />

                <div className="marquee flex gap-4 py-5 px-4">
                  {animatedApps.map((app, idx) => (
                    <button
                      key={`${app.slug}-${idx}`}
                      onClick={() => go(routeForApp(app.slug))}
                      className="min-w-[280px] max-w-[280px] rounded-2xl border border-slate-800 bg-slate-950/55 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
                    >
                      <div className="flex items-center justify-between gap-2">
                        <div className="text-lg font-bold text-slate-100">{app.title}</div>
                        {app.status ? (
                          <span className="rounded-full border border-slate-700 bg-slate-900/40 px-2 py-1 text-xs text-slate-200">
                            {app.status}
                          </span>
                        ) : null}
                      </div>

                      <div className="mt-2 text-sm text-slate-300">{app.subtitle}</div>

                      <div className="mt-3 flex items-center justify-between">
                        {app.nudge ? (
                          <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                            {app.nudge}
                          </span>
                        ) : <span />}

                        <span className="text-xs text-slate-500">Open â†’</span>
                      </div>
                    </button>
                  ))}
                </div>
              </div>
            </div>
          );
        })}
      </section>

      <style jsx>{`
        .marquee {
          width: max-content;
          animation: marquee 90s linear infinite;
        }
        @keyframes marquee {
          0% { transform: translateX(0); }
          100% { transform: translateX(-33.333%); }
        }
      `}</style>
    </main>
  );
}








