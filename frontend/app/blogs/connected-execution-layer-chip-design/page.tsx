"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["4-8 handoffs", "A typical chip journey crosses requirements, RTL, verification, implementation, firmware/software, validation, and product review."],
  ["30-50%", "Engineering time can be lost to setup, handoff, rerun, report review, and context reconstruction in fragmented flows."],
  ["1 run record", "ChipLoop keeps workflow ID, logs, artifacts, dashboards, ZIPs, and Ask This Run attached to the execution record."],
];

const rows = [
  ["AI model", "Generates or reviews text/code", "Needs workflow context, real tool evidence, and controlled handoff"],
  ["EDA tool", "Runs a specific task", "Needs orchestration, inputs, logs, artifact capture, and review"],
  ["Engineer", "Makes design and signoff decisions", "Needs traceable evidence, not disconnected files"],
  ["Execution layer", "Connects intent, tools, agents, dashboards, and products", "Turns isolated tasks into repeatable silicon journeys"],
];

export default function ConnectedExecutionLayerChipDesignPage() {
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
          Why Chip Design Needs a Connected Execution Layer
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          AI models can generate useful output, and EDA tools can run powerful checks. The missing layer is connected execution: the system that keeps intent, tools, evidence, dashboards, and handoffs together.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Problem Is Not Just Generation</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            In real silicon development, a generated RTL file is only the beginning. The team still needs checks, reports, debug, synthesis, verification, implementation, software, validation, and product-level review.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            Traditional flows spread this work across scripts, terminals, folders, dashboards, emails, and meetings. Every handoff creates a chance to lose context.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          {metrics.map(([value, body]) => (
            <div key={value} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-center">
              <div className="text-3xl font-extrabold text-cyan-300">{value}</div>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Layer</div>
            <div>What it does</div>
            <div>What it needs</div>
          </div>
          {rows.map(([layer, role, need]) => (
            <div key={layer} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{layer}</div>
              <div>{role}</div>
              <div>{need}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Where ChipLoop Fits</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            ChipLoop is the connected execution layer for silicon work. Products define the journey. Apps run repeatable workflows. Studio lets teams create custom agents and workflows. Dashboards, logs, artifacts, ZIPs, HEM, and Smart Context keep the work inspectable.
          </p>
        </section>
      </article>
    </main>
  );
}
