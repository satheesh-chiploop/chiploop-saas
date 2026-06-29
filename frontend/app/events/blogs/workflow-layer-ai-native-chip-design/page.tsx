"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function WorkflowLayerAiNativeChipDesignPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="events" showMarketplace showSettings={false} />
      <article className="mx-auto max-w-4xl px-4 py-10 sm:px-6">
        <button
          type="button"
          onClick={() => router.push("/events")}
          className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
        >
          Back to Events
        </button>

        <div className="mt-8 text-xs font-semibold uppercase tracking-wide text-cyan-300">Events Blog</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          Why ChipLoop Is Building the Workflow Layer for AI-Native Chip Design
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          AI chip design will not be won by prompt boxes alone. The durable layer is workflow orchestration: intent, tools, artifacts, evidence, review, and handoffs.
        </p>

        <section className="mt-8 rounded-xl border border-cyan-900/70 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">The Core Idea</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            ChipLoop sits between AI models, EDA tools, and engineering teams. It turns design intent into repeatable loops, captures the evidence from each run, and helps teams move to the next stage with context.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          {["Intent", "Execution", "Evidence"].map((item) => (
            <div key={item} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-cyan-300">{item}</h3>
              <p className="mt-3 text-sm leading-6 text-slate-300">
                {item === "Intent"
                  ? "Capture what the engineer wants to build and which loop should run."
                  : item === "Execution"
                    ? "Configure agents, apps, tools, and workflows around the task."
                    : "Preserve logs, artifacts, dashboards, summaries, and review context."}
              </p>
            </div>
          ))}
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why This Matters</h2>
          <p className="leading-8">
            Semiconductor workflows are complex because every stage depends on prior context. A generated RTL file is only useful if teams can trace the requirement, run checks, inspect failures, and hand the result to verification or implementation.
          </p>
          <p className="leading-8">
            ChipLoop makes that context productized. Apps, reference journeys, Studio workflows, Products, dashboards, downloads, and Ask This Run create a platform surface around AI-assisted chip work.
          </p>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Layer</div>
            <div>Point Solution</div>
            <div>ChipLoop Platform</div>
          </div>
          {[
            ["AI", "Generate an answer", "Operate inside a workflow"],
            ["EDA", "Run a tool", "Attach tool output to run evidence"],
            ["Review", "Manual artifact hunt", "Ask and inspect the run"],
          ].map(([layer, point, platform]) => (
            <div key={layer} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{layer}</div>
              <div>{point}</div>
              <div>{platform}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why It Matters</h2>
          <p className="leading-8">
            The opportunity is not a single AI feature. It is the workflow layer where AI, tools, data, and engineering review meet. That layer can expand across RTL, verification, synthesis, physical design, embedded software, validation, and product journeys.
          </p>
        </section>
      </article>
    </main>
  );
}
