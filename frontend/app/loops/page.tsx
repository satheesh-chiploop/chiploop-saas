"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const loops = [
  {
    name: "Digital Design",
    body: "Requirements, design intent, architecture-to-RTL, RTL quality, verification setup, smoke checks, and handoff.",
    core: "Spec capture, Arch2RTL, RTL review, smoke compile/sim, DQA, basic verification setup.",
    advanced: "Spec2RTL conformance, deeper DQA, assertions, coverage planning, verification closure analysis.",
    analytics: {
      core: { agents: 28, apps: 4, workflows: 2, journeys: 4 },
      advanced: { agents: 18, apps: 4, workflows: 3, journeys: 5 },
    },
    href: "/apps?loop=digital",
  },
  {
    name: "Digital Implementation",
    body: "Synthesis, constraints, timing/power/area reports, DFT/MBIST, RTL-to-GDS, STA, signoff, and tapeout handoff.",
    core: "Synthesis setup, synthesis run, synthesis readiness, constraints review, timing/area/power reports.",
    advanced: "Auto synthesis closure, LEC, scan/DFT, ATPG, MBIST insertion, RTL-to-GDS, STA, signoff closure.",
    analytics: {
      core: { agents: 8, apps: 2, workflows: 1, journeys: 2 },
      advanced: { agents: 31, apps: 4, workflows: 3, journeys: 3 },
    },
    href: "/apps/system-pd",
  },
  {
    name: "Mixed Signal",
    body: "System and mixed-signal integration across digital RTL, analog models, SoC intent, system simulation, and synthesis.",
    core: "System RTL, analog/digital interface intent, behavioral models, smoke tests, System Sim, System Synthesis.",
    advanced: "System DQA, integration debug, mixed-signal verification evidence, System PD/signoff path, validation handoff.",
    analytics: {
      core: { agents: 35, apps: 5, workflows: 2, journeys: 1 },
      advanced: { agents: 42, apps: 8, workflows: 4, journeys: 2 },
    },
    href: "/apps?loop=system",
  },
  {
    name: "Firmware/Software",
    body: "Register extraction, HAL, drivers, boot/diagnostics, firmware builds, software services, co-simulation, and demos.",
    core: "Register-map extraction, HAL/driver scaffolds, boot setup, diagnostics, firmware build/run.",
    advanced: "Software SDK/API generation, package validation, hardware/software co-simulation, integration debug, demo package.",
    analytics: {
      core: { agents: 27, apps: 4, workflows: 1, journeys: 4 },
      advanced: { agents: 35, apps: 7, workflows: 3, journeys: 5 },
    },
    href: "/apps?loop=embedded",
  },
  {
    name: "Validation",
    body: "Validation plans, bench/instrument setup, connectivity intent, wiring, sequences, preflight, execution, and learning.",
    core: "Test plans, bench setup, instrument setup, connectivity/wiring intent, preflight, run review.",
    advanced: "Execution orchestration, analytics, pattern detection, coverage proposals, plan evolution.",
    analytics: {
      core: { agents: 10, apps: 3, workflows: 1, journeys: 2 },
      advanced: { agents: 7, apps: 2, workflows: 1, journeys: 4 },
    },
    href: "/apps?loop=validation",
  },
];

const metricLabels = [
  ["agents", "Agents"],
  ["apps", "Apps"],
  ["workflows", "Workflows"],
  ["journeys", "Product / Ref Journeys"],
] as const;

const metricMax = {
  agents: 50,
  apps: 10,
  workflows: 5,
  journeys: 6,
} as const;

export default function LoopsPage() {
  const router = useRouter();
  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="loops" showMarketplace showSettings={false} />
      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Explore Design Loops</div>
          <h1 className="mt-3 text-4xl font-extrabold tracking-tight sm:text-5xl">Choose the chip design loops you need.</h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Each subscription loop has Core and Advanced capability. Core lets users generate, configure,
            run, and review normal flows. Advanced adds deeper analysis, closure, debug, signoff,
            validation, and automation.
          </p>
        </div>
        <div className="mt-8 grid gap-5 md:grid-cols-2 xl:grid-cols-5">
          {loops.map((loop) => (
            <article key={loop.name} className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
              <h2 className="text-xl font-bold text-cyan-300">{loop.name}</h2>
              <p className="mt-3 min-h-28 text-sm leading-6 text-slate-300">{loop.body}</p>
              <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/70 p-3">
                <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">Current coverage</div>
                <div className="mt-3 space-y-3">
                  {metricLabels.map(([key, label]) => {
                    const coreValue = loop.analytics.core[key];
                    const advancedValue = loop.analytics.advanced[key];
                    const coreWidth = `${Math.max((coreValue / metricMax[key]) * 100, 5)}%`;
                    const advancedWidth = `${Math.max((advancedValue / metricMax[key]) * 100, 5)}%`;
                    return (
                      <div key={key}>
                        <div className="mb-1 flex items-center justify-between gap-3 text-xs">
                          <span className="font-semibold text-slate-400">{label}</span>
                          <span className="text-slate-500">Core {coreValue} / Adv {advancedValue}</span>
                        </div>
                        <div className="space-y-1">
                          <div className="flex items-center gap-2">
                            <span className="w-14 text-[11px] font-bold uppercase tracking-wide text-slate-500">Core</span>
                            <div className="h-2 flex-1 overflow-hidden rounded-full bg-slate-900">
                              <div className="h-full rounded-full bg-slate-400" style={{ width: coreWidth }} />
                            </div>
                          </div>
                          <div className="flex items-center gap-2">
                            <span className="w-14 text-[11px] font-bold uppercase tracking-wide text-cyan-500">Advanced</span>
                            <div className="h-2 flex-1 overflow-hidden rounded-full bg-slate-900">
                              <div className="h-full rounded-full bg-cyan-300" style={{ width: advancedWidth }} />
                            </div>
                          </div>
                        </div>
                      </div>
                    );
                  })}
                </div>
              </div>
              <div className="mt-4 space-y-3 text-sm">
                <div className="rounded-lg border border-slate-800 bg-slate-950/70 p-3">
                  <div className="font-bold text-slate-100">Core</div>
                  <p className="mt-1 leading-5 text-slate-400">{loop.core}</p>
                </div>
                <div className="rounded-lg border border-cyan-900/60 bg-cyan-950/20 p-3">
                  <div className="font-bold text-cyan-100">Advanced</div>
                  <p className="mt-1 leading-5 text-slate-400">{loop.advanced}</p>
                </div>
              </div>
              <button
                onClick={() => router.push(loop.href)}
                className="mt-5 rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
              >
                Explore {loop.name}
              </button>
            </article>
          ))}
        </div>
        <p className="mt-4 text-sm leading-6 text-slate-500">
          Coverage counts reflect the current prebuilt frontend catalog and backend agent/workflow registry. Some agents are shared across product stages and loops.
        </p>
        <section className="mt-10 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-extrabold text-white">How product journeys unlock</h2>
          <p className="mt-3 max-w-4xl leading-7 text-slate-300">
            Product journeys are not sold as a separate subscription loop. They become available when
            the required loops are subscribed. For example, a digital IP journey with synthesis needs
            Digital Design Core plus Digital Implementation Core. Closure, signoff, LEC, MBIST, and
            RTL-to-GDS paths require the corresponding Advanced loop.
          </p>
          <div className="mt-5 flex flex-wrap gap-3">
            <button onClick={() => router.push("/products")} className="rounded-lg bg-cyan-500 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400">
              Explore Products
            </button>
            <button onClick={() => router.push("/pricing")} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              View Pricing
            </button>
          </div>
        </section>
      </section>
    </main>
  );
}
