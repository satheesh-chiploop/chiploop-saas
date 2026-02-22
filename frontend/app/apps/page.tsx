// ✅ AFTER: app_apps_page.tsx (minimal edits only)

"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

type LoopType = "digital" | "validation" | "analog" | "embedded" | "system";

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
  digital: { title: "Digital Loop", tagline: "Design → RTL → Verify → Improve", accent: "accent-digital" },
  validation: { title: "Validation Loop", tagline: "Plan → Run → Learn → Improve", accent: "accent-validation" },
  analog: { title: "Analog Loop", tagline: "Analyze → Simulate → Correlate → Improve", accent: "accent-analog" },
  embedded: { title: "Embedded(Firmware) Loop", tagline: "Code → Run → Observe → Fix", accent: "accent-embedded" },
  system: { title: "System Loop", tagline: "Integrate → Analyze → Optimize", accent: "accent-system" },
};

export default function AppsHomePage() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);

  const [view, setView] = useState<"recommended" | "all">("recommended");

  useEffect(() => {
    let mounted = true;
    (async () => {
      const { data: { user } } = await supabase.auth.getUser();
      if (!mounted) return;
      setUserEmail(user?.email ?? null);
    })();
    return () => { mounted = false; };
  }, []);

  // ✅ updated apps list (only change is digital apps)
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

    // ✅ NEW DIGITAL FLAGSHIPS
    {
      slug: "arch2rtl",
      title: "Arch2RTL",
      subtitle: "Spec → Architecture → Microarch → RTL → Handoff package",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Most used",
      promise: "Generate RTL + docs + handoff artifacts",
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
      subtitle: "Text → Integration intent → Top RTL + report",
      loop_type: "digital",
      status: "Flagship",
      nudge: "New",
      promise: "Assemble IPs into a runnable top",
    },

    {
      slug: "validation-plan",
      title: "Validation Plan & Coverage",
      subtitle: "Datasheet/spec → test plan + coverage map + gaps",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Structured plan + coverage gaps in one shot",
    },
    {
      slug: "bench-setup",
      title: "Bench Setup",
      subtitle: "Register instruments → create bench → schematic → preflight",
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
      subtitle: "Analyze past runs → patterns → evolve plan + coverage",
      loop_type: "validation",
      status: "Flagship",
      nudge: "New",
      promise: "Turn history into next test improvements",
    },

    // ✅ NEW ANALOG APPS
    {
      slug: "analog-run",
      title: "Analog Run",
      subtitle: "Spec → Netlist → Model → Validate → Correlate → Iterate",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Recommended",
      promise: "End-to-end analog loop",
    },
    {
      slug: "analog-spec",
      title: "Analog Spec",
      subtitle: "Text → structured spec + open questions",
      loop_type: "analog",
      status: "Flagship",
      nudge: "Most used",
      promise: "Clean spec JSON",
    },
    {
      slug: "analog-netlist",
      title: "Analog Netlist",
      subtitle: "Spec → SPICE scaffold + sim plan",
      loop_type: "analog",
      status: "Flagship",
      nudge: "New",
      promise: "Netlist + sim plan",
    },
    {
      slug: "analog-model",
      title: "Analog Model",
      subtitle: "Spec → SV RNM / Verilog-A behavioral model",
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

    // ✅ EMBEDDED (production firmware chain)
    {
      slug: "embedded-run",
      title: "Embedded Run",
      subtitle: "End-to-end firmware flow: HAL → Drivers → Boot → Diagnostics → Co-sim → Report",
      loop_type: "embedded",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Production-ready firmware package + exec summary",
    },
    {
      slug: "embedded-hal",
      title: "Embedded HAL",
      subtitle: "Register extraction → Rust HAL layer → validation",
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
      subtitle: "Logs → fault classification → root cause → fix plan",
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
    {
      slug: "system-intelligence-analyzer",
      title: "System Intelligence Analyzer",
      subtitle: "Power/perf bottlenecks across blocks",
      loop_type: "system",
      status: "Coming",
      promise: "System-level recommendations",
    },
  ]), []);

  const featured = apps.find(a => a.slug === "validation-run") || apps[0];

  const FLAGSHIP_SLUGS = new Set<string>([
    // Validation (1–2)
    "validation-run",
    "bench-setup",

    // Digital (1–2)
    "arch2rtl",
    "dqa",

    // Analog (1–2)
    "analog-run",
    "analog-model",

    // Embedded (1–2)
    "embedded-run",
    "embedded-driver",
  ]);

  const flagship = apps.filter(a => a.status === "Flagship" && FLAGSHIP_SLUGS.has(a.slug));

  const loops: LoopType[] = useMemo(() => (["validation", "digital", "analog", "embedded", "system"]), []);

  const go = (path: string) => router.push(path);


  

  const routeForApp = (slug: string) => {
    // ✅ Dedicated pages (apps with custom UX)

    const dedicated: Record<string, string> = {
      // Validation (dedicated pages)
      "validation-run": "/apps/validation-run",
      "validation-plan": "/apps/validation-plan",
      "bench-setup": "/apps/bench-setup",
      "preflight": "/apps/preflight",
      "validation-insights": "/apps/validation-insights",
    
      // Digital (dedicated pages)
      "arch2rtl": "/apps/arch2rtl",
      "integrate": "/apps/integrate",
      "dqa": "/apps/dqa",
      "verify": "/apps/verify",
      "smoke": "/apps/smoke",

      // ✅ ANALOG
      "analog-run": "/apps/analog-run",
      "analog-spec": "/apps/analog-spec",
      "analog-netlist": "/apps/analog-netlist",
      "analog-model": "/apps/analog-model",
      "analog-validate-model": "/apps/analog-validate-model",
      "analog-correlate": "/apps/analog-correlate",
      "analog-iterate": "/apps/analog-iterate",
      "analog-abstracts": "/apps/analog-abstracts",

      // ✅ EMBEDDED (dedicated pages)
      "embedded-hal": "/apps/embedded-hal",
      "embedded-driver": "/apps/embedded-driver",
      "embedded-boot": "/apps/embedded-boot",
      "embedded-diagnostics": "/apps/embedded-diagnostics",
      "embedded-log-analyzer": "/apps/embedded-log-analyzer",
      "embedded-validate": "/apps/embedded-validate",
      "embedded-run": "/apps/embedded-run",
    };
    
    return dedicated[slug] || `/apps/${slug}`;
  };

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      {/* Top bar */}
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button
            className="flex items-center gap-2 text-xl font-extrabold"
            onClick={() => go("/apps")}
            title="Apps Home"
          >
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">Apps</span>
          </button>

          <div className="flex items-center gap-3">
            <button
              onClick={() => go("/workflow")}
              className="rounded-xl bg-slate-800 px-4 py-2 text-slate-200 hover:bg-slate-700 transition"
              title="Advanced Builder"
            >
              Studio
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

      {/* Hero */}
      <section className="mx-auto max-w-6xl px-6 pt-10 pb-6">
        <div className="grid gap-4 md:grid-cols-5">
          <div className="md:col-span-3 rounded-2xl border border-slate-800 bg-slate-900/30 p-6 shadow-lg">
            <div className="flex items-start justify-between gap-4">
              <div>
                <div className="text-xs text-slate-400">
                  Welcome{userEmail ? `, ${userEmail}` : ""} • <span className="text-cyan-300">Start here</span>
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
                    Progressive outputs • Executive summary • ZIP artifacts
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
                <div className="mt-1 text-sm text-slate-400">Bench → instruments → preflight → run → report</div>
              </button>

              {/* ✅ change this to Arch2RTL */}
              <button
                onClick={() => go("/apps/arch2rtl")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Digital - Spec → RTL + handoff</div>
                  <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                    Most used
                  </span>
                </div>
                <div className="mt-1 text-sm text-slate-400"> Digital - Arch2RTL: docs + SV + package</div>
              </button>

              {/* ✅ NEW: Analog daily-use */}
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
                  <div className="mt-1 text-sm text-slate-400">Analog Run: netlist → model → validate → correlate</div>
              </button>

              {/* ✅ NEW: Embedded daily-use */}
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
                  <div className="mt-1 text-sm text-slate-400">Embedded Run: HAL → drivers → boot → diagnostics → report</div>
              </button>
            </div>



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
              <div className="mt-4 text-xs text-slate-500">One click → progressive outputs → ZIP</div>
            </button>
          ))}
        </div>
      </section>

      {/* Loop rows */}
      <section className="mx-auto max-w-6xl px-6 pb-16 space-y-10">
        {(view === "recommended" ? loops.filter(l => l === "digital" || l === "analog" || l === "embedded" || l === "validation" ) : loops).map((loop) => {
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

                        <span className="text-xs text-slate-500">Open →</span>
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
