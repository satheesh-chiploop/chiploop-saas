"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const leverageMetrics = [
  ["3x", "Target productivity leverage for early-stage teams by reducing manual setup, handoff, and review loops."],
  ["5 loops", "Digital Design, Digital Implementation, Mixed Signal, Firmware/Software, and Validation can be connected through one platform."],
  ["195+ agents", "Specialized agents can be orchestrated across requirements, RTL, verification, implementation, software, validation, and demos."],
];

const journey = [
  ["Define", "Capture requirement, design intent, constraints, and product goal."],
  ["Generate", "Run apps or workflows for RTL, specs, handoff packages, and supporting collateral."],
  ["Check", "Run quality, verification, synthesis, implementation, or validation stages."],
  ["Inspect", "Use dashboards, ZIPs, logs, Ask This Run, and Smart Context to understand results."],
  ["Continue", "Use Products or HEM Automatic Runs to move to the next selected stage."],
];

export default function OneEngineerFullSiliconWorkflowPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="blogs" showMarketplace showSettings={false} />
      <article className="mx-auto max-w-4xl px-4 py-10 sm:px-6">
        <button
          type="button"
          onClick={() => router.push("/blogs")}
          className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
        >
          Back to Blogs
        </button>

        <div className="mt-8 text-xs font-semibold uppercase text-cyan-300">ChipLoop Blog</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          From One Engineer to a Full Silicon Workflow
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          The future IC engineer will not replace every specialist. But with connected AI workflows, one engineer or a small team can move much further across the silicon journey before needing large handoff-heavy teams.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Why This Is Changing</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Chip development has traditionally required many specialists because every stage has its own tools, scripts, assumptions, and review habits. Agentic AI changes what is possible, but only if the work remains connected.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            ChipLoop gives engineers a single platform to define, configure, run, inspect, and continue workflows across design, implementation, firmware/software, validation, and product demos.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          {leverageMetrics.map(([value, body]) => (
            <div key={value} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-center">
              <div className="text-3xl font-extrabold text-cyan-300">{value}</div>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">A Practical Journey</h2>
          <div className="mt-5 grid gap-3">
            {journey.map(([step, body], index) => (
              <div key={step} className="grid gap-3 rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300 sm:grid-cols-[64px_0.35fr_1fr]">
                <div className="font-bold text-cyan-300">{String(index + 1).padStart(2, "0")}</div>
                <div className="font-semibold text-slate-100">{step}</div>
                <div>{body}</div>
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">The Productivity Shift</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            The goal is not to hide engineering judgment. The goal is to remove repeated setup, disconnected handoffs, manual artifact hunting, and unclear next steps, so engineers spend more time making design decisions and less time reconstructing context.
          </p>
        </section>
      </article>
    </main>
  );
}
