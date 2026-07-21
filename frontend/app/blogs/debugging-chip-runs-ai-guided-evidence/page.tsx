"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["70-90%", "Debug time can be spent finding the right log, report, artifact, or failing stage before analysis even begins."],
  ["1 question", "Ask This Run lets users ask about warnings, failures, missing outputs, and recommended next steps from run evidence."],
  ["60-85%", "Smart Context can reduce unnecessary context for focused debug questions by selecting relevant evidence first."],
];

const debugFlow = [
  ["Detect", "Workflow status, product run logs, and HEM summaries show which stage failed."],
  ["Open", "The failed workflow dashboard keeps logs, artifacts, ZIP downloads, and run summary together."],
  ["Ask", "Ask This Run uses real run context to summarize likely causes and next inspection points."],
  ["Inspect", "Smart Context prioritizes relevant logs, reports, summaries, and artifact paths."],
  ["Rerun", "Use stage settings, product rerun, or HEM continuation policy to move forward after fixes."],
];

export default function DebuggingChipRunsAiGuidedEvidencePage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="blogs" showMarketplace showSettings={false} />
      <article className="mx-auto max-w-4xl px-4 py-10 sm:px-6">
        <button type="button" onClick={() => router.push("/blogs")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
          Back to Blogs
        </button>

        <div className="mt-8 text-xs font-semibold uppercase text-cyan-300">ChipLoop Blog</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          Debugging Chip Runs with AI-Guided Evidence
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Failure debug is one of the most practical places for AI in chip design, but only when the answer is grounded in real run evidence: logs, reports, artifacts, dashboards, and stage history.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Real Debug Bottleneck</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            When synthesis, verification, or tapeout fails, the first question is often not the technical root cause. It is: where is the right evidence?
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            Engineers may search through terminal logs, generated reports, artifact folders, and old run directories before they can start debugging. ChipLoop brings that evidence to the run surface.
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

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">A Better Debug Flow</h2>
          <div className="mt-5 grid gap-3">
            {debugFlow.map(([step, body], index) => (
              <div key={step} className="grid gap-3 rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300 sm:grid-cols-[64px_0.35fr_1fr]">
                <div className="font-bold text-cyan-300">{String(index + 1).padStart(2, "0")}</div>
                <div className="font-semibold text-slate-100">{step}</div>
                <div>{body}</div>
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Why Evidence-Guided AI Matters</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            AI debug becomes useful when it is attached to the run, not guessing from a generic prompt. ChipLoop keeps the evidence close to the question, so answers can point users toward the failed stage, relevant report, missing artifact, or next rerun step.
          </p>
        </section>
      </article>
    </main>
  );
}
