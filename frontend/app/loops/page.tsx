"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

type MetricKey = "agents" | "apps" | "workflows" | "journeys";

const loops = [
  {
    name: "Digital Design",
    short: "From requirements to RTL and verification-ready handoff.",
    core: "RTL, DQA, smoke checks",
    advanced: "Spec2RTL, assertions, closure analysis",
    href: "/apps?loop=digital",
    metrics: { agents: 46, apps: 8, workflows: 5, journeys: 5 },
  },
  {
    name: "Digital Implementation",
    short: "From synthesis to closure, signoff, and tapeout handoff.",
    core: "Synthesis, constraints, reports",
    advanced: "LEC, MBIST, RTL-to-GDS, signoff",
    href: "/apps/system-pd",
    metrics: { agents: 39, apps: 6, workflows: 4, journeys: 3 },
  },
  {
    name: "Mixed Signal",
    short: "Connect digital RTL, analog models, and system-level execution.",
    core: "System RTL, Sim, Synthesis",
    advanced: "Integration debug, System PD, validation handoff",
    href: "/apps?loop=system",
    metrics: { agents: 77, apps: 13, workflows: 6, journeys: 2 },
  },
  {
    name: "Firmware/Software",
    short: "Build drivers, firmware, software services, and co-simulation flows.",
    core: "HAL, drivers, firmware build",
    advanced: "SDK/API, co-sim, package validation",
    href: "/apps?loop=embedded",
    metrics: { agents: 62, apps: 11, workflows: 4, journeys: 5 },
  },
  {
    name: "Validation",
    short: "Plan benches, run validation, learn from results, and improve coverage.",
    core: "Plans, bench setup, preflight",
    advanced: "Orchestration, analytics, plan evolution",
    href: "/apps?loop=validation",
    metrics: { agents: 17, apps: 5, workflows: 2, journeys: 4 },
  },
];

const metrics: Array<{ key: MetricKey; label: string; color: string }> = [
  { key: "agents", label: "Agents", color: "bg-cyan-300" },
  { key: "apps", label: "Apps", color: "bg-violet-400" },
  { key: "workflows", label: "Workflows", color: "bg-amber-300" },
  { key: "journeys", label: "Journeys", color: "bg-emerald-300" },
];

const chartMax = 80;

const unlockExamples = [
  ["Digital IP with synthesis", "Digital Design + Digital Implementation"],
  ["Mixed-signal product", "Mixed Signal + Firmware/Software + Validation"],
  ["Full product handoff", "Design + Implementation + Software + Validation"],
];

const referenceJourneys = [
  {
    title: "PWM Controller",
    body: "A compact digital IP journey from RTL to firmware, software validation, and product app.",
    href: "/apps#reference-journeys",
  },
  {
    title: "Temperature Monitor SoC",
    body: "A mixed-signal journey with digital RTL, analog model, System Sim, firmware, software, and validation.",
    href: "/apps#reference-journeys",
  },
  {
    title: "SRAM MBIST",
    body: "A memory and DFT journey with synthesis, scan/ATPG readiness, MBIST evidence, and implementation handoff.",
    href: "/apps#reference-journeys",
  },
];

export default function LoopsPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="loops" showMarketplace showSettings={false} />

      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-4 py-12 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="mx-auto max-w-4xl text-center">
          <div className="text-xs font-semibold uppercase text-cyan-300">Explore Design Loops</div>
          <h1 className="mt-3 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">
            Start with one loop. Grow into a complete chip journey.
          </h1>
          <p className="mt-5 text-lg leading-8 text-slate-300">
            Start with the loop you need. Expand from design to implementation, software, validation,
            and product journeys as your chip matures.
          </p>
          <p className="mt-3 text-xl font-extrabold text-slate-100">Core gets you moving. Advanced helps you close.</p>
          <div className="mt-7 flex flex-col justify-center gap-3 sm:flex-row">
            <button onClick={() => router.push("/pricing")} className="rounded-lg bg-cyan-500 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400">
              View Pricing
            </button>
            <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              Explore Apps
            </button>
            <button onClick={() => router.push("/products")} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              Explore Products
            </button>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="grid gap-4 md:grid-cols-2 xl:grid-cols-5">
          {loops.map((loop) => (
            <button
              key={loop.name}
              onClick={() => router.push(loop.href)}
              className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-left transition hover:border-cyan-500 hover:bg-slate-900"
            >
              <h2 className="text-xl font-extrabold text-white">{loop.name}</h2>
              <p className="mt-3 min-h-20 text-sm leading-6 text-slate-300">{loop.short}</p>
              <div className="mt-4 text-xs font-semibold uppercase text-slate-500">Explore loop</div>
            </button>
          ))}
        </div>
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className="text-xs font-semibold uppercase text-cyan-300">Platform Coverage</p>
            <h2 className="mt-3 text-3xl font-extrabold leading-tight text-white sm:text-4xl">
              Coverage grows across the chip journey.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              Each loop brings specialized agents, apps, workflows, and product journeys into one connected platform.
            </p>
          </div>

          <div className="mt-8 flex flex-wrap gap-4 text-sm text-slate-300">
            {metrics.map((metric) => (
              <div key={metric.key} className="flex items-center gap-2">
                <span className={`h-3 w-3 rounded-sm ${metric.color}`} />
                <span>{metric.label}</span>
              </div>
            ))}
          </div>

          <div className="mt-8 overflow-x-auto">
            <div className="min-w-[980px]">
              <div className="grid grid-cols-[60px_1fr] gap-4">
                <div className="relative h-80 border-r border-slate-800 text-right text-xs text-slate-500">
                  <span className="absolute right-3 top-0 -translate-y-1/2">80</span>
                  <span className="absolute right-3 top-1/4 -translate-y-1/2">60</span>
                  <span className="absolute right-3 top-1/2 -translate-y-1/2">40</span>
                  <span className="absolute right-3 top-3/4 -translate-y-1/2">20</span>
                  <span className="absolute bottom-0 right-3 translate-y-1/2">0</span>
                </div>

                <div>
                  <div className="relative h-80 border-b border-slate-700">
                    <div className="pointer-events-none absolute inset-x-0 bottom-0 top-0 flex flex-col justify-between">
                      <span className="border-t border-slate-800" />
                      <span className="border-t border-slate-800" />
                      <span className="border-t border-slate-800" />
                      <span className="border-t border-slate-800" />
                      <span className="border-t border-slate-700" />
                    </div>

                    <div className="relative grid h-full grid-cols-5 items-end gap-6 px-2">
                      {loops.map((loop) => (
                        <div key={loop.name} className="flex h-full items-end justify-center gap-1.5">
                          {metrics.map((metric) => {
                            const value = loop.metrics[metric.key];
                            const height = `${Math.max((value / chartMax) * 100, 4)}%`;
                            return (
                              <div key={metric.key} className="flex h-full w-7 flex-col items-center justify-end gap-1">
                                <div className="text-xs font-bold text-slate-200">{value}</div>
                                <div className={`w-full rounded-t-md ${metric.color}`} style={{ height }} title={`${loop.name} ${metric.label}: ${value}`} />
                              </div>
                            );
                          })}
                        </div>
                      ))}
                    </div>
                  </div>

                  <div className="mt-4 grid grid-cols-5 gap-6 px-2 text-center">
                    {loops.map((loop) => (
                      <div key={loop.name} className="text-xs font-bold leading-4 text-slate-100">{loop.name}</div>
                    ))}
                  </div>
                  <div className="mt-3 text-center text-xs font-semibold uppercase text-slate-500">Design loops</div>
                </div>
              </div>
            </div>
          </div>
          <p className="mt-5 text-sm leading-6 text-slate-500">
            Counts reflect the current prebuilt frontend catalog and backend agent/workflow registry. Some agents are shared across loops and product stages.
          </p>
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className="text-xs font-semibold uppercase text-cyan-300">Core vs Advanced</p>
            <h2 className="mt-3 text-3xl font-extrabold leading-tight text-white sm:text-4xl">
              Core gets you moving. Advanced helps you close.
            </h2>
          </div>
          <div className="mt-6 overflow-x-auto">
            <table className="w-full min-w-[900px] text-left text-sm">
              <thead className="bg-slate-950/80 text-slate-300">
                <tr>
                  <th className="px-4 py-3 font-semibold">Loop</th>
                  <th className="px-4 py-3 font-semibold">Core</th>
                  <th className="px-4 py-3 font-semibold">Advanced</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-800">
                {loops.map((loop) => (
                  <tr key={loop.name}>
                    <td className="px-4 py-3 font-bold text-slate-100">{loop.name}</td>
                    <td className="px-4 py-3 text-slate-300">{loop.core}</td>
                    <td className="px-4 py-3 text-slate-300">{loop.advanced}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className="text-xs font-semibold uppercase text-cyan-300">Product Journeys</p>
            <h2 className="mt-3 text-3xl font-extrabold leading-tight text-white sm:text-4xl">
              Product journeys unlock as loops connect.
            </h2>
          </div>
          <div className="mt-6 grid gap-4 md:grid-cols-3">
            {unlockExamples.map(([title, body]) => (
              <article key={title} className="rounded-xl border border-slate-800 bg-slate-950/70 p-5">
                <h3 className="text-lg font-extrabold text-white">{title}</h3>
                <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
              </article>
            ))}
          </div>
          <div className="mt-7 flex flex-wrap gap-3">
            <button onClick={() => router.push("/products")} className="rounded-lg bg-cyan-500 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400">
              Explore Products
            </button>
            <button onClick={() => router.push("/pricing")} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              View Pricing
            </button>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1680px]">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className="text-xs font-semibold uppercase text-cyan-300">Reference Journeys</p>
            <h2 className="mt-3 text-3xl font-extrabold leading-tight text-white sm:text-4xl">
              Try a journey that already connects the loops.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              Start with a guided example, inspect the outputs, then adapt the flow to your own product.
            </p>
          </div>
          <div className="mt-6 grid gap-4 md:grid-cols-3">
            {referenceJourneys.map((journey) => (
              <button
                key={journey.title}
                onClick={() => router.push(journey.href)}
                className="rounded-xl border border-slate-800 bg-slate-950/70 p-5 text-left transition hover:border-cyan-500 hover:bg-slate-950"
              >
                <h3 className="text-lg font-extrabold text-white">{journey.title}</h3>
                <p className="mt-3 min-h-20 text-sm leading-6 text-slate-300">{journey.body}</p>
                <div className="mt-4 text-xs font-semibold uppercase text-slate-500">Open reference journey</div>
              </button>
            ))}
          </div>
        </div>
        </div>
      </section>
    </main>
  );
}
