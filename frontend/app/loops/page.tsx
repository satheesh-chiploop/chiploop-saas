"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const loops = [
  {
    name: "Digital",
    body: "Specs to RTL, DQA, verification, synthesis, tapeout, and IP handoff.",
    href: "/apps?loop=digital",
  },
  {
    name: "Analog",
    body: "Specs, behavioral models, SPICE/netlist, abstract views, GDS collateral, and LEF/LIB consistency.",
    href: "/apps?loop=analog",
  },
  {
    name: "Embedded",
    body: "Register extraction, HAL, drivers, firmware validation, and co-simulation.",
    href: "/apps?loop=embedded",
  },
  {
    name: "System",
    body: "Digital, analog, firmware, and software integration across System RTL, simulation, DQA, PD, and product apps.",
    href: "/apps?loop=system",
  },
  {
    name: "Validation",
    body: "Bench setup, instruments, test plans, hardware runs, coverage, and insights.",
    href: "/apps?loop=validation",
  },
  {
    name: "Physical Design",
    body: "Synthesis, floorplan, placement, CTS, route, DRC/LVS, logic equivalence, and tapeout handoff.",
    href: "/apps/system-pd",
  },
  {
    name: "Products",
    body: "Multi-stage product journeys that orchestrate workflows, dashboards, artifacts, and handoff context end to end.",
    href: "/products",
  },
];

export default function LoopsPage() {
  const router = useRouter();
  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav showMarketplace showSettings={false} />
      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Explore Loops</div>
          <h1 className="mt-3 text-4xl font-extrabold tracking-tight sm:text-5xl">One Platform. Many Chip Design Loops.</h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Choose the chip design loop you want to execute. Each loop connects purpose-built agents, prebuilt workflows,
            configuration settings, dashboards, and handoff packages.
          </p>
        </div>
        <div className="mt-8 grid gap-5 md:grid-cols-2 xl:grid-cols-3">
          {loops.map((loop) => (
            <article key={loop.name} className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
              <h2 className="text-xl font-bold text-cyan-300">{loop.name}</h2>
              <p className="mt-3 min-h-24 text-sm leading-6 text-slate-300">{loop.body}</p>
              <button
                onClick={() => router.push(loop.href)}
                className="mt-5 rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
              >
                Open {loop.name}
              </button>
            </article>
          ))}
        </div>
      </section>
    </main>
  );
}
