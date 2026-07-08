"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const rows = [
  ["One platform", "Separate tools per loop", "Products, Apps, and Studio in one place"],
  ["Ask this run", "Users inspect logs and artifacts manually", "Ask about the run, summarize loops, and get recommended next steps"],
  ["Run across loops", "Teams stitch loop execution manually", "Run within one loop or across multiple loops"],
  ["Architecture to RTL", "Architecture intent converts through manual setup", "Move from architecture intent to RTL execution"],
  ["Repair loops", "Fixes stay local to one tool", "Repair and iterate within a loop or across connected loops"],
  ["Scalability", "Execution slows as projects grow", "Reusable templates scale across products and teams"],
  ["Connected context", "Context scattered across files and chats", "Specs, settings, logs, artifacts, and handoffs stay connected"],
  ["Tool integration", "New tools require custom glue code", "Add tools and pick the right tool per workflow"],
  ["Process technology", "Flows tied to one PDK or environment", "Process-technology agnostic orchestration"],
  ["Developer access", "Browser and automation live separately", "Use the same context from UI, SDK, CLI, IDE, and CI"],
  ["Reusable execution", "Hard to reproduce setup", "Reusable workflows, agents, and run settings"],
  ["Run visibility", "Debug requires manual artifact chasing", "Run logs, dashboards, artifacts, and ZIPs stay attached"],
  ["Handoff quality", "Artifacts handed over without context", "Dashboards, reports, and ZIPs travel with the run"],
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
      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-4 py-10 sm:px-6 sm:py-14">
        <div className="mx-auto max-w-[1680px]">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase text-cyan-300">Why ChipLoop</div>
          <h1 className="mt-3 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">
            One Platform for Connected Chip Execution
          </h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Traditional chip development spreads execution across separate tools, custom scripts, emails, folders,
            and review meetings. ChipLoop keeps the loops connected so design intent, run configuration, logs,
            artifacts, dashboards, and handoff context move together.
          </p>
        </div>

        <div className="mt-8 overflow-hidden rounded-xl border border-slate-800 bg-slate-900/80">
          <div className="grid grid-cols-1 bg-slate-950 text-sm font-bold text-slate-200 md:grid-cols-[0.8fr_1fr_1fr]">
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

        <section className="mt-10 rounded-xl border border-slate-800 bg-slate-950/70 p-6 sm:p-8">
          <h2 className="text-3xl font-extrabold leading-tight text-white sm:text-4xl">Design Intent to Execution</h2>
          <div className="mt-6 grid grid-cols-1 items-stretch gap-4 md:grid-cols-[1fr_auto_1fr_auto_1fr]">
            {[
              ["01", "Define", "Product, app, or workflow"],
              ["02", "Configure", "Stages, tools, and goals"],
              ["03", "Run", "Logs, dashboards, and ZIPs"],
            ].map(([step, title, body], index) => (
              <div key={title} className="contents">
                <div className="rounded-xl border border-slate-800 bg-slate-900/65 p-5 text-center">
                  <div className="mx-auto flex h-10 w-10 items-center justify-center rounded-full bg-cyan-400 text-sm font-extrabold text-slate-950">
                    {step}
                  </div>
                  <h3 className="mt-4 text-lg font-extrabold text-white">{title}</h3>
                  <p className="mt-2 text-sm leading-6 text-slate-300">{body}</p>
                </div>
                {index < 2 ? (
                  <div className="flex items-center justify-center text-3xl font-extrabold text-white md:px-2">
                    <span className="hidden md:inline">{"\u2192"}</span>
                    <span className="md:hidden">{"\u2193"}</span>
                  </div>
                ) : null}
              </div>
            ))}
          </div>
          <div className="mt-7 flex flex-col gap-3 sm:flex-row sm:flex-wrap">
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
        </div>
      </section>
    </main>
  );
}
