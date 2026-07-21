"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const priorities = [
  {
    rank: 1,
    problem: "Lost engineering context",
    industryPain: "Specs, RTL, logs, reports, and review notes live in separate places.",
    chiploopAnswer: "Run-centered memory with artifacts, dashboards, ZIPs, and Ask This Run.",
  },
  {
    rank: 2,
    problem: "AI output without accountability",
    industryPain: "Generated RTL or scripts may look useful but still need checks and evidence.",
    chiploopAnswer: "Connect generation to verification, synthesis, reports, and review.",
  },
  {
    rank: 3,
    problem: "Manual handoffs between loops",
    industryPain: "Teams rebuild context when moving from architecture to RTL, verification, implementation, or validation.",
    chiploopAnswer: "Reference journeys and apps carry intent, configuration, and artifacts forward.",
  },
  {
    rank: 4,
    problem: "Hard-to-review EDA output",
    industryPain: "Reports are verbose, tool-specific, and scattered across folders.",
    chiploopAnswer: "Evidence dashboards plus Ask This Run make failures and next steps easier to inspect.",
  },
  {
    rank: 5,
    problem: "Startup tools are hard to adopt",
    industryPain: "Useful point tools struggle to enter real engineering workflows.",
    chiploopAnswer: "Tools can plug in as apps, agents, workflow stages, or product journeys.",
  },
];

export default function TopFiveChipLoopIndustryProblemsPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="events" showMarketplace showSettings={false} />
      <article className="mx-auto max-w-5xl px-4 py-10 sm:px-6">
        <button
          type="button"
          onClick={() => router.push("/events")}
          className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
        >
          Back to Blogs
        </button>

        <div className="mt-8 text-xs font-semibold uppercase text-cyan-300">ChipLoop Blog</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          Top 5 Industry Problems ChipLoop Addresses
        </h1>
        <p className="mt-5 max-w-3xl text-lg leading-8 text-slate-300">
          ChipLoop is not just an AI prompt surface. It is a workflow layer for moving chip work from intent to evidence.
        </p>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-[64px_1fr_1.2fr_1.2fr] bg-slate-900 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div className="p-3">Rank</div>
            <div className="p-3">Problem</div>
            <div className="p-3">Industry Pain</div>
            <div className="p-3">ChipLoop Answer</div>
          </div>
          {priorities.map((item) => (
            <div key={item.rank} className="grid grid-cols-[64px_1fr_1.2fr_1.2fr] border-t border-slate-800 bg-slate-950/60 text-sm text-slate-300">
              <div className="p-3 font-bold text-cyan-300">{item.rank}</div>
              <div className="p-3 font-semibold text-slate-100">{item.problem}</div>
              <div className="p-3 leading-6">{item.industryPain}</div>
              <div className="p-3 leading-6">{item.chiploopAnswer}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Simple Model</h2>
          <div className="mt-5 grid gap-3 text-center text-sm font-semibold text-slate-100 sm:grid-cols-5">
            {["Define", "Configure", "Run", "Review", "Continue"].map((step, index) => (
              <div key={step} className="rounded-lg border border-cyan-800 bg-slate-950/50 p-4">
                <div>{step}</div>
                {index < 4 ? <div className="mt-2 text-xs text-slate-500">next loop</div> : null}
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why These Five First?</h2>
          <p className="leading-8">
            The biggest bottleneck in chip design is not only generation speed. It is preserving context, proving outputs, and moving cleanly between engineering stages. ChipLoop focuses there: guided journeys, tool-backed runs, saved artifacts, run review, and repeatable handoffs.
          </p>
          <p className="leading-8">
            That is why run-centered memory is priority one. Once every run is traceable, AI assistance, startup tools, verification loops, synthesis loops, and product journeys can become part of one connected engineering system.
          </p>
        </section>
      </article>
    </main>
  );
}
