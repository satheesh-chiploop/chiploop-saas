"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const loops = [
  {
    name: "Digital Design",
    body: "Requirements, design intent, spec-to-RTL, arch-to-RTL, RTL generation, RTL review, and handoff.",
    core: "Spec capture, basic design intent analysis, RTL generation/review, smoke simulation.",
    advanced: "Spec-to-RTL checks, advanced analyzer, assertions, interface checks, iterative refinement.",
    href: "/apps?loop=digital",
  },
  {
    name: "Digital Implementation",
    body: "Synthesis, constraints, timing/power/area reports, closure, RTL-to-GDS, STA, and tapeout handoff.",
    core: "Synthesis setup, synthesis run, readiness review, constraints review, basic reports.",
    advanced: "Auto synthesis closure, LEC, DFT/MBIST, RTL-to-GDS, STA, signoff closure.",
    href: "/apps/system-pd",
  },
  {
    name: "Mixed Signal",
    body: "Mixed-signal requirements, system partitioning, analog/digital interfaces, System RTL, and System Synthesis.",
    core: "System RTL, analog/digital models, smoke tests, basic verification, System Synthesis.",
    advanced: "Mixed-signal closure, integration debug, model refinement, signoff support, validation handoff.",
    href: "/apps?loop=system",
  },
  {
    name: "Firmware/Software",
    body: "Firmware, drivers, software examples, software validation, co-simulation, integration debug, and demos.",
    core: "Firmware skeleton, register-map use, drivers, examples, build/run, basic validation.",
    advanced: "Firmware/software validation loops, hardware/software co-simulation, debug, demo package.",
    href: "/apps?loop=embedded",
  },
  {
    name: "Validation",
    body: "Validation plans, bring-up checklists, test cases, logs, dashboards, debug, and readiness packages.",
    core: "Validation plan, bring-up checklist, basic test cases, log review, dashboard summary.",
    advanced: "Debug assistant, root cause, regression review, validation closure, release readiness.",
    href: "/apps?loop=validation",
  },
];

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
