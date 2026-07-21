"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function FutureEndToEndIcEngineerPage() {
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
          The Future End-to-End IC Engineer
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Agentic AI and generative AI tools are changing what an IC engineer can do. The future engineer will not only specialize in one task. They will be able to move across requirements, architecture, RTL, verification, implementation, software, validation, and product context with tool-backed assistance.
        </p>

        <div className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-sm leading-7 text-slate-300">
          Generative AI creates or transforms content. Agentic AI plans, uses tools, checks results, and helps iterate. ChipLoop connects both into engineering loops with artifacts, evidence, and handoffs.
        </div>

        <div className="mt-10 space-y-9 text-slate-300">
          <section>
            <h2 className="text-2xl font-bold text-white">From Specialist Tasks to End-to-End Ownership</h2>
            <p className="mt-3 leading-8">
              Chip design has always required deep specialization. RTL engineers, verification engineers, physical design engineers, firmware developers, validation engineers, and product engineers each bring important expertise. That specialization will remain valuable.
            </p>
            <p className="mt-3 leading-8">
              What changes with AI is the ability for one engineer to understand and navigate more of the full path. An engineer can define a requirement, generate or inspect RTL, configure verification, run synthesis, review reports, ask what failed, and understand what needs to move forward. They may not replace every expert, but they can operate with more end-to-end context.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Generative AI vs Agentic AI</h2>
            <p className="mt-3 leading-8">
              Generative AI is the right term when a model creates content: RTL drafts, testbench ideas, assertions, documentation, configuration snippets, scripts, summaries, or review notes. It is powerful, but generation alone is not enough for chip work.
            </p>
            <p className="mt-3 leading-8">
              Agentic AI adds workflow behavior. It can take a goal, choose steps, call tools, inspect outputs, detect missing evidence, and propose the next action. In IC design, this matters because requirements must become executable workflows, and generated artifacts must be checked against real tool results.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-3">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Generate</h3>
              <p className="mt-3 text-sm leading-6">
                Create candidate RTL, tests, constraints, scripts, summaries, and documentation from design intent.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Check</h3>
              <p className="mt-3 text-sm leading-6">
                Run tools, inspect logs, surface warnings, verify outputs, and avoid treating generated content as proven.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Iterate</h3>
              <p className="mt-3 text-sm leading-6">
                Use requirements and tool feedback to repair, tune, rerun, and carry evidence into the next loop.
              </p>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Fix and Iterate Based on Requirements</h2>
            <p className="mt-3 leading-8">
              Requirements are not static text. They create obligations: interfaces, timing, reset behavior, register maps, safety checks, coverage goals, firmware expectations, validation measurements, and product behavior. The future IC engineer needs tools that can keep those obligations visible while the design evolves.
            </p>
            <p className="mt-3 leading-8">
              Agentic workflows can help close this loop. If a run fails, the system can preserve the failure context, identify the relevant artifacts, suggest a repair path, and rerun the right stage. If a requirement changes, the engineer can trace which loops need to be updated instead of manually searching across files and reports.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">The Bottleneck in Current Ways of Working</h2>
            <p className="mt-3 leading-8">
              Today, many teams work through disconnected tools, shared folders, chat messages, scripts, spreadsheets, dashboards, and review meetings. A tool might be excellent at one task, but the handoff into the next task is still manual. That creates friction every time context moves.
            </p>
            <p className="mt-3 leading-8">
              The bottleneck is not only tool quality. It is integration. Engineers spend too much time translating requirements into setup, moving artifacts between stages, explaining what happened in a run, and rebuilding context after a failure. This slows down both large teams and small startups.
            </p>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-2xl font-bold text-white">Startup Tools Need an Easier Path In</h2>
            <p className="mt-4 leading-8">
              Many startup tools are strong at one part of the chip lifecycle: better RTL generation, better verification planning, better formal checks, better physical design analytics, better validation automation, or better report understanding. The hard part is getting those tools into the daily engineering flow.
            </p>
            <p className="mt-3 leading-8">
              ChipLoop can help by giving startup tools a workflow surface: define inputs, declare outputs, run inside an app or Studio workflow, preserve artifacts, and expose results through dashboards and Ask This Run. Instead of asking every tool to become a full platform, ChipLoop can make specialized tools easier to plug into connected loops.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-2">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Current Integration Pattern</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Custom scripts for each environment</li>
                <li>- Manual artifact movement</li>
                <li>- Separate dashboards and reports</li>
                <li>- Hard-to-repeat demos and pilots</li>
                <li>- Long path from useful tool to trusted workflow</li>
              </ul>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">ChipLoop Integration Pattern</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Tool becomes a loop, app, agent, or workflow stage</li>
                <li>- Inputs and outputs stay attached to the run</li>
                <li>- Artifacts are captured for review and download</li>
                <li>- Ask This Run can inspect the tool evidence</li>
                <li>- Teams can evaluate startup tools in end-to-end context</li>
              </ul>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">How ChipLoop Helps the Future Engineer</h2>
            <p className="mt-3 leading-8">
              ChipLoop gives engineers a place to define, configure, run, review, and continue. It supports guided apps, reference journeys, custom Studio workflows, product journeys, artifacts, logs, dashboards, downloads, and Ask This Run. That makes it easier for an engineer to move across the chip lifecycle without losing the engineering story.
            </p>
            <p className="mt-3 leading-8">
              The future IC engineer will still need judgment. AI will not replace signoff discipline, domain expertise, or careful review. But with agentic workflows and integrated tools, one engineer can cover more ground, understand more context, and collaborate across domains with stronger evidence.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">The Direction</h2>
            <p className="mt-3 leading-8">
              The future is not just generative AI writing files. It is generative AI plus agentic workflows plus real tools plus connected context. That combination can help engineers fix and iterate based on requirements, integrate new tools faster, and move from idea to evidence more efficiently.
            </p>
            <p className="mt-3 leading-8">
              ChipLoop is designed for that transition: a platform where engineers and tools can work across the full loop, not just one prompt or one isolated task.
            </p>
          </section>
        </div>
      </article>
    </main>
  );
}
