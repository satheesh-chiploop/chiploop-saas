"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function AgenticAiFutureChipDesignPage() {
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
          Agentic AI and the Future of Chip Design
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          AI is entering chip design in several forms: assistants, copilots, workflow agents, and orchestration around traditional EDA environments. The future is not one technique replacing everything else. It is these techniques working together with engineering evidence.
        </p>

        <div className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-sm leading-7 text-slate-300">
          Agentic AI is most useful when it can plan, run, inspect, and hand off work across real engineering loops instead of producing isolated text.
        </div>

        <div className="mt-10 space-y-9 text-slate-300">
          <section>
            <h2 className="text-2xl font-bold text-white">The Traditional Foundation Still Matters</h2>
            <p className="mt-3 leading-8">
              Chip design has a mature tool ecosystem. Commercial EDA environments, reference flows, foundry collateral, signoff rules, PDKs, verification infrastructure, and internal company methodology are not going away. Teams still need proven flows for synthesis, simulation, timing, physical implementation, DRC, LVS, power, and signoff.
            </p>
            <p className="mt-3 leading-8">
              Environments and reference flows commonly built around major EDA platforms, including Cadence-style digital and custom design environments, give teams repeatability and trust. They encode years of engineering method. The opportunity for AI is not to ignore that foundation, but to help engineers navigate it more effectively.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-2">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Traditional EDA and Reference Flows</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Proven toolchains and signoff methodology</li>
                <li>- Company-specific scripts, constraints, checks, and reports</li>
                <li>- Strong for deterministic execution and formal review</li>
                <li>- Often hard for new users to navigate end to end</li>
              </ul>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">AI-Native Workflow Layer</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Captures intent and setup choices</li>
                <li>- Helps select, configure, and run the right loop</li>
                <li>- Summarizes evidence and missing outputs</li>
                <li>- Connects handoffs across engineering domains</li>
              </ul>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Technique 1: AI Assistance</h2>
            <p className="mt-3 leading-8">
              AI assistance is the simplest entry point. It helps explain a protocol, draft RTL, review a warning, summarize a report, or write a small script. This is useful because it reduces friction and makes expert knowledge easier to access.
            </p>
            <p className="mt-3 leading-8">
              The limitation is context. Assistance can answer a question, but it does not automatically know which run produced which artifact, whether a generated file was used downstream, or what evidence is required for the next stage.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Technique 2: Copilots</h2>
            <p className="mt-3 leading-8">
              Copilots bring AI closer to the engineering environment. They can help inside an editor, notebook, terminal, or design review flow. A copilot can improve productivity by staying close to the active task.
            </p>
            <p className="mt-3 leading-8">
              Copilots are strongest when the task is local: edit this RTL, explain this block, suggest a test, or help with a command. But chip design also needs larger workflow memory: what has run, what passed, what failed, and what should be handed off.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Technique 3: Agentic Workflows</h2>
            <p className="mt-3 leading-8">
              Agentic workflows move beyond one-off assistance. They can plan a sequence, call tools, generate artifacts, inspect outputs, retry within limits, and produce summaries. In chip design, that means an agent can participate in architecture-to-RTL, verification, synthesis, implementation setup, validation, or product journeys.
            </p>
            <p className="mt-3 leading-8">
              The key requirement is discipline. An agentic workflow should not invent a signoff result or hide missing evidence. It should preserve what happened, expose failures, and make the next engineering action clearer.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Technique 4: Reference Flow Orchestration</h2>
            <p className="mt-3 leading-8">
              Traditional reference flows remain important because they provide trusted tool recipes. A company may already have a Cadence-based flow, a foundry reference flow, an OpenROAD/OpenLane flow, or an internal methodology that engineers rely on.
            </p>
            <p className="mt-3 leading-8">
              Agentic AI can help at the edges of these flows: preparing inputs, checking configuration, explaining failures, summarizing reports, routing artifacts to the next step, and guiding users through the workflow. The AI layer should respect the tool environment rather than pretend to replace it.
            </p>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-2xl font-bold text-white">Where ChipLoop Fits</h2>
            <p className="mt-4 leading-8">
              ChipLoop focuses on the workflow layer. It helps users define intent, configure the right run, execute connected loops, inspect artifacts, and ask questions about completed runs. That makes AI assistance and agentic execution part of a traceable engineering journey.
            </p>
            <p className="mt-3 leading-8">
              Instead of treating AI as a chat box beside the flow, ChipLoop brings AI into the loop structure: Apps, reference journeys, Studio workflows, Products, dashboards, downloads, and Ask This Run.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-3">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Assist</h3>
              <p className="mt-3 text-sm leading-6">
                Explain, draft, summarize, and accelerate local engineering tasks.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Orchestrate</h3>
              <p className="mt-3 text-sm leading-6">
                Move from intent to configured workflows and tool-backed execution.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Review</h3>
              <p className="mt-3 text-sm leading-6">
                Preserve logs, artifacts, reports, and evidence so teams can decide what comes next.
              </p>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">The Future Is Connected</h2>
            <p className="mt-3 leading-8">
              The future of chip design will include AI assistants, copilots, agentic workflows, and traditional EDA reference flows. The winning pattern is not replacing engineering judgment. It is giving engineers better ways to move through complexity with context.
            </p>
            <p className="mt-3 leading-8">
              Agentic AI can help teams explore faster, configure smarter, run more repeatably, and review evidence more clearly. That is where AI becomes more than a prompt. It becomes part of the engineering system.
            </p>
          </section>
        </div>
      </article>
    </main>
  );
}
