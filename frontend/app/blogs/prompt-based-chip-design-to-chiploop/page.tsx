"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function PromptBasedChipDesignToChipLoopPage() {
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
          From Prompt-Based Chip Design to ChipLoop-Based Design
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Prompt-based chip design showed that AI can help engineers move faster. ChipLoop takes the next step: connected workflows where intent, tools, generated artifacts, checks, evidence, and handoffs stay together.
        </p>

        <div className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-sm leading-7 text-slate-300">
          Webinar cadence: ChipLoop webinars run once every two weeks at 9:00 AM PST, starting July 11, 2026.
        </div>

        <div className="mt-10 space-y-9 text-slate-300">
          <section>
            <h2 className="text-2xl font-bold text-white">Prompting Was the First Step</h2>
            <p className="mt-3 leading-8">
              The first wave of AI-assisted chip design was prompt-based. Engineers asked a model to write RTL, explain a protocol, draft a testbench, create constraints, or summarize a report. That was useful because it made expert tasks feel more accessible and reduced blank-page friction.
            </p>
            <p className="mt-3 leading-8">
              But chip design is not a single answer. A design has requirements, revisions, interfaces, generated files, simulation results, synthesis reports, timing evidence, verification gaps, and product decisions. A prompt can create content, but it does not automatically preserve the workflow context that makes the content trustworthy.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Where Traditional Flows Break Down</h2>
            <p className="mt-3 leading-8">
              Traditional semiconductor workflows move through many disconnected tools and handoffs. Architecture intent becomes RTL, RTL moves into verification, constraints move into implementation, reports move into review meetings, and decisions often live in documents, chat threads, or local folders.
            </p>
            <p className="mt-3 leading-8">
              That fragmentation creates avoidable risk. Teams lose track of which spec produced which RTL, which run generated which warnings, whether constraints match the current top module, and what evidence is strong enough for the next stage. The more domains involved, the harder it becomes to keep the design story coherent.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">What Changes with ChipLoop</h2>
            <p className="mt-3 leading-8">
              ChipLoop treats chip design as a connected journey instead of isolated prompts. A user can start with intent, run a guided app or reference journey, inspect generated artifacts, ask questions about the run, and carry evidence forward into the next loop.
            </p>
            <p className="mt-3 leading-8">
              The important difference is continuity. ChipLoop keeps the source of truth in the platform: workflow metadata, logs, generated RTL, constraints, reports, dashboards, ZIP downloads, and Ask This Run context. The output is not just a model response. It is a run with traceable evidence.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-2">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Traditional or Prompt-Only</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- One-off answers and copied files</li>
                <li>- Manual tool setup and brittle handoffs</li>
                <li>- Reports reviewed outside the design context</li>
                <li>- Hard to know what changed between runs</li>
                <li>- Missing evidence can stay hidden until late</li>
              </ul>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">ChipLoop-Based</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Guided apps and reference journeys</li>
                <li>- Connected loops across RTL, verification, implementation, embedded, validation, and products</li>
                <li>- Artifacts, logs, dashboards, and summaries preserved per run</li>
                <li>- Ask This Run grounded in actual workflow evidence</li>
                <li>- Clearer handoff from one engineering stage to the next</li>
              </ul>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">The Transition</h2>
            <p className="mt-3 leading-8">
              Prompt-based design is still valuable, but it is best treated as one capability inside a larger system. ChipLoop makes that system visible. It gives engineers a place to run, inspect, compare, and continue design work instead of restarting context with every prompt.
            </p>
            <p className="mt-3 leading-8">
              The shift is from asking an AI to produce a chip artifact to using an AI-native workflow platform to move chip work forward with evidence. That is the transition from prompt-based chip design to ChipLoop-based chip design.
            </p>
          </section>
        </div>
      </article>
    </main>
  );
}
