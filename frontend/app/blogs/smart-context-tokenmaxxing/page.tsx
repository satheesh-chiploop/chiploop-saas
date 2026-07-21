"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metricCards = [
  ["60-85%", "Estimated context reduction for focused run questions when logs and reports are large."],
  ["2 modes", "Smart Context for focused inspection, Full Context when broad review is needed."],
  ["Run + Project", "Available in Ask This Run and Ask this Project, including uploaded files and GitHub context."],
];

const comparisonRows = [
  ["Full Context", "Sends the broader available run or project package.", "Useful for first-pass broad review, but can spend tokens on unrelated files."],
  ["Smart Context", "Ranks logs, reports, artifacts, and files against the user's question.", "Useful for failures, summaries, next-step questions, and cost-aware inspection."],
];

export default function SmartContextTokenmaxxingPage() {
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
          Smart Context: Tokenmaxxing for Practical Silicon Workflows
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Smart Context helps ChipLoop answer engineering questions with the right evidence instead of blindly sending every log, report, and file to the model.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Why This Matters</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Semiconductor workflows generate a lot of context: specs, RTL, reports, logs, summaries, dashboards, timing output, verification results, and handoff files. More context is not always better. It can increase cost, slow responses, and bury the real signal.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            Smart Context is ChipLoop&apos;s practical tokenmaxxing layer. It estimates how much context would be used in a full review, then builds a smaller evidence pack based on the user&apos;s question.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          {metricCards.map(([value, body]) => (
            <div key={value} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-center">
              <div className="text-3xl font-extrabold text-cyan-300">{value}</div>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">A Simple Example</h2>
          <p className="leading-8">
            Suppose a synthesis run produces 90,000 characters of logs, reports, summaries, and artifacts. A user asks: &quot;Why did synthesis fail and what should I inspect first?&quot;
          </p>
          <p className="leading-8">
            Full Context may include the entire available package. Smart Context instead prioritizes the workflow status, failure log tail, synthesis summary, LEC or timing reports, and artifact index entries that mention errors or warnings. A typical focused pack may be closer to 15,000-25,000 characters.
          </p>
          <p className="leading-8">
            Using the rough estimate of four characters per token, that can move a question from about 22,500 tokens to about 4,000-6,250 tokens. The exact number depends on the run, but the direction is important: fewer irrelevant tokens, faster inspection, and lower model cost.
          </p>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Mode</div>
            <div>How it works</div>
            <div>Best use</div>
          </div>
          {comparisonRows.map(([mode, how, use]) => (
            <div key={mode} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{mode}</div>
              <div>{how}</div>
              <div>{use}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">How It Works in ChipLoop</h2>
          <div className="mt-4 space-y-3 text-slate-300">
            <p className="leading-8">
              In Ask This Run, Smart Context starts with workflow metadata, status, logs, artifact index, and text artifacts. It ranks evidence using the user&apos;s question and gives priority to failures, warnings, summaries, reports, dashboards, and handoff files.
            </p>
            <p className="leading-8">
              In Ask this Project, Smart Context works across uploaded files, pasted content, folders, and selected GitHub files. It ranks project files by relevance, then sends the most useful files first.
            </p>
            <p className="leading-8">
              After the answer, ChipLoop shows the Smart estimate, Full estimate, estimated reduction, and how many evidence items were included. The goal is to make context usage visible, not hidden.
            </p>
          </div>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">The Bigger Direction</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            HEM helps ChipLoop continue successful workflows automatically. Smart Context helps users inspect those runs efficiently. Together, they move ChipLoop toward self-regulated silicon workflows: run the next step, preserve evidence, and help engineers understand what happened without wasting time or tokens.
          </p>
        </section>
      </article>
    </main>
  );
}
