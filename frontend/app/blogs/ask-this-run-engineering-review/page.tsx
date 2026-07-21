"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function AskThisRunEngineeringReviewPage() {
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
          Back to Blogs
        </button>

        <div className="mt-8 text-xs font-semibold uppercase text-cyan-300">ChipLoop Blog</div>
        <h1 className="mt-3 text-4xl font-extrabold leading-tight tracking-tight sm:text-5xl">
          Why Ask This Run Changes Engineering Review
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Engineering review is not just reading one final answer. It is understanding what was generated, what failed, what changed, what evidence exists, and what should happen next.
        </p>

        <div className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-sm leading-7 text-slate-300">
          Ask This Run turns a completed workflow into a reviewable engineering object: logs, artifacts, summaries, warnings, and context can be queried from the run itself.
        </div>

        <div className="mt-10 space-y-9 text-slate-300">
          <section>
            <h2 className="text-2xl font-bold text-white">Review Usually Starts with Artifact Hunting</h2>
            <p className="mt-3 leading-8">
              In a traditional flow, an engineer often starts review by opening folders, logs, generated RTL, reports, scripts, constraints, and dashboards. The question is rarely just whether the run passed. The real question is what the run means.
            </p>
            <p className="mt-3 leading-8">
              A failed synthesis run may still produce a netlist candidate. A verification run may pass some tests but leave coverage gaps. An implementation run may produce reports while missing a key signoff artifact. Engineers need to inspect the evidence, not just the top-level status.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">A Run Has Context</h2>
            <p className="mt-3 leading-8">
              ChipLoop stores workflow metadata, logs, artifact indexes, generated files, summaries, and downloadable packages around the run. Ask This Run uses that context to help users ask practical engineering questions after execution.
            </p>
            <p className="mt-3 leading-8">
              The benefit is not that review becomes automatic. The benefit is that review starts from the evidence already produced by the workflow, instead of forcing users to manually reconstruct the run from scattered outputs.
            </p>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-2xl font-bold text-white">Questions Engineers Actually Ask</h2>
            <ul className="mt-5 space-y-3 text-sm leading-6">
              <li>- What was generated in this run?</li>
              <li>- What failed, and where is the evidence?</li>
              <li>- Which warnings should I inspect first?</li>
              <li>- Are expected outputs missing?</li>
              <li>- Is this RTL ready for verification?</li>
              <li>- Is this netlist ready for downstream physical design?</li>
              <li>- What should I do next?</li>
            </ul>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Why This Matters Across Loops</h2>
            <p className="mt-3 leading-8">
              RTL, verification, synthesis, physical design, firmware, validation, and product journeys each produce different evidence. A verification loop may care about failing tests and coverage. A synthesis loop may care about Yosys checks, timing, unmapped cells, and generated netlists. A validation loop may care about bench readiness, measurements, and instrument results.
            </p>
            <p className="mt-3 leading-8">
              Ask This Run gives the user a consistent review entry point across those loops. The questions change by domain, but the review pattern stays familiar: ask about the run, inspect the evidence, decide the next step.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-2">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Without Run-Grounded Review</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Users hunt through files and logs manually</li>
                <li>- Important warnings can be missed</li>
                <li>- Review depends on memory of how the run was configured</li>
                <li>- Handoffs require separate summaries</li>
              </ul>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">With Ask This Run</h3>
              <ul className="mt-4 space-y-3 text-sm leading-6">
                <li>- Questions are grounded in that workflow run</li>
                <li>- Artifacts and logs stay part of the review context</li>
                <li>- Users can ask for failures, missing outputs, or next steps</li>
                <li>- Review becomes easier to repeat across loops</li>
              </ul>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Voice Makes Review More Natural</h2>
            <p className="mt-3 leading-8">
              Engineers often think through review out loud: what changed, why did it fail, what should be checked first, and whether the result is ready for the next stage. Voice input makes Ask This Run faster for that style of review because users can capture the question while the context is fresh.
            </p>
            <p className="mt-3 leading-8">
              The important part is still the same: the question is tied to the run. Whether typed or spoken, the review starts from workflow evidence.
            </p>
          </section>
        </div>
      </article>
    </main>
  );
}
