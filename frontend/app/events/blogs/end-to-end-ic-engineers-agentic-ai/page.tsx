"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function EndToEndIcEngineersAgenticAiPage() {
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

        <div className="mt-8 text-xs font-semibold uppercase tracking-wide text-cyan-300">Investor View</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          From Specialist Teams to End-to-End IC Engineers
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Agentic AI can expand engineering leverage by helping one engineer move across more of the chip lifecycle while still preserving expert review and tool-backed evidence.
        </p>

        <section className="mt-8 rounded-xl border border-cyan-900/70 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">The Productivity Thesis</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            The future IC engineer will not replace every specialist. But they will define, configure, run, inspect, and iterate across more stages with AI and tool assistance.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
            <h3 className="text-lg font-bold text-cyan-300">Before</h3>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              Work moves between specialists through files, meetings, scripts, and manual context transfer.
            </p>
          </div>
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
            <h3 className="text-lg font-bold text-cyan-300">With AI</h3>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              Engineers can generate, summarize, repair, and reason faster, but still need evidence.
            </p>
          </div>
          <div className="rounded-xl border border-cyan-900/70 bg-cyan-950/20 p-5">
            <h3 className="text-lg font-bold text-cyan-300">With ChipLoop</h3>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              AI assistance is connected to workflows, artifacts, dashboards, and run-grounded review.
            </p>
          </div>
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why This Is Investable</h2>
          <p className="leading-8">
            Semiconductor engineering is expensive because each stage requires specialized knowledge and careful handoff. Agentic AI can reduce coordination cost by helping engineers navigate tasks that used to require multiple disconnected tools and teams.
          </p>
          <p className="leading-8">
            ChipLoop makes that leverage usable by wrapping the work in loops: define the goal, configure the run, execute the workflow, review the evidence, and continue to the next stage.
          </p>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Market</div>
            <div>Pain</div>
            <div>ChipLoop Fit</div>
          </div>
          {[
            ["Startups", "Small teams need broader coverage", "More end-to-end velocity"],
            ["Enterprises", "Handoffs and review slow teams down", "Workflow memory and evidence"],
            ["Education", "Students need guided context", "Reference journeys and apps"],
          ].map(([market, pain, fit]) => (
            <div key={market} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{market}</div>
              <div>{pain}</div>
              <div>{fit}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Investor Takeaway</h2>
          <p className="leading-8">
            The core value is engineering leverage. ChipLoop can help teams do more with the same people by connecting AI-generated work to real execution, review, and iteration. That makes the platform relevant to startups, enterprise teams, and training markets.
          </p>
        </section>
      </article>
    </main>
  );
}
