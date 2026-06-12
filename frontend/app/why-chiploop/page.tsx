"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const rows = [
  ["One platform", "Separate tools per loop", "Products, Apps, and Studio in one place"],
  ["Connected context", "Context scattered across files and chats", "Specs, settings, logs, artifacts, and handoffs stay connected"],
  ["Reusable execution", "Hard to reproduce setup", "Reusable workflows, agents, and run settings"],
  ["Run visibility", "Debug requires manual artifact chasing", "Run logs, dashboards, artifacts, and ZIPs stay attached"],
  ["Workflow control", "Custom scripts for every variation", "Configurable stages, tools, agents, and goals"],
  ["Product tracking", "Progress tracked manually", "Product-level stages, history, and results"],
];

const actions = [
  ["Explore Products", "/products"],
  ["Explore Apps", "/apps"],
  ["Explore Studio", "/workflow"],
];

export default function WhyChipLoopPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav showMarketplace showSettings={false} />
      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Why ChipLoop</div>
          <h1 className="mt-3 text-4xl font-extrabold tracking-tight sm:text-5xl">
            One Platform for Connected Chip Execution
          </h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Traditional chip development spreads execution across separate tools, custom scripts, emails, folders,
            and review meetings. ChipLoop keeps the loops connected so design intent, run configuration, logs,
            artifacts, dashboards, and handoff context move together.
          </p>
        </div>

        <div className="mt-8 overflow-hidden rounded-xl border border-slate-800 bg-slate-900/80">
          <div className="grid grid-cols-1 bg-slate-950 text-sm font-bold text-cyan-200 md:grid-cols-[0.8fr_1fr_1fr]">
            <div className="border-b border-slate-800 p-4 md:border-b-0 md:border-r">Feature</div>
            <div className="border-b border-slate-800 p-4 md:border-b-0 md:border-r">Traditional</div>
            <div className="p-4">ChipLoop</div>
          </div>
          {rows.map(([feature, traditional, chiploop]) => (
            <div key={feature} className="grid grid-cols-1 border-t border-slate-800 text-sm leading-6 md:grid-cols-[0.8fr_1fr_1fr]">
              <div className="border-b border-slate-800 p-4 font-semibold text-slate-100 md:border-b-0 md:border-r">{feature}</div>
              <div className="flex gap-3 border-b border-slate-800 p-4 text-slate-400 md:border-b-0 md:border-r">
                <span className="mt-0.5 inline-flex h-5 w-5 shrink-0 items-center justify-center rounded border border-rose-400/50 text-xs font-bold text-rose-300">X</span>
                <span>{traditional}</span>
              </div>
              <div className="flex gap-3 p-4 text-slate-100">
                <span className="mt-0.5 inline-flex h-5 w-5 shrink-0 items-center justify-center rounded border border-emerald-400/60 text-xs font-bold text-emerald-300">✓</span>
                <span>{chiploop}</span>
              </div>
            </div>
          ))}
        </div>

        <section className="mt-10 rounded-xl border border-cyan-400/30 bg-cyan-400/10 p-6 sm:p-8">
          <h2 className="text-2xl font-extrabold">Define. Configure. Run. Review. Improve.</h2>
          <p className="mt-3 max-w-4xl leading-7 text-slate-300">
            Start from a product, a prebuilt app, or a custom Studio workflow. Configure the settings each loop needs,
            run the agents, then review dashboards and downloadable handoff packages from the same product context.
          </p>
          <div className="mt-6 flex flex-col gap-3 sm:flex-row sm:flex-wrap">
            {actions.map(([label, href], index) => (
              <button
                key={label}
                onClick={() => router.push(href)}
                className={`rounded-lg px-5 py-3 text-sm font-bold transition ${
                  index === 0
                    ? "bg-cyan-400 text-slate-950 hover:bg-cyan-300"
                    : "border border-slate-700 text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
                }`}
              >
                {label}
              </button>
            ))}
          </div>
        </section>
      </section>
    </main>
  );
}
