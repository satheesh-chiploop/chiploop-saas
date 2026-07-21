"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["3 closure loops", "Verification, synthesis, and physical-design closure can each follow analyze, repair, rerun, and summarize."],
  ["1-3 iterations", "Early closure loops often benefit from a small bounded iteration budget instead of open-ended automation."],
  ["4 PD checks", "LEF, timing, DRC, and LVS are key evidence points for physical-design repair loops."],
];

const closureRows = [
  ["Verification closure", "Coverage gaps, failing tests, missing checkers, weak stimulus", "Analyze failures and coverage, add testcase/seed intent, update plan, rerun verification, summarize closure status"],
  ["Synthesis closure", "Timing miss, area/power concern, LEC mismatch, tool warnings", "Classify root issue, adjust constraints/options, optionally rerun synthesis, check LEC and readiness"],
  ["PD closure: LEF", "Missing pins, abstract mismatch, bad macro interface", "Inspect abstract collateral, repair pin/interface metadata, regenerate handoff collateral"],
  ["PD closure: Timing", "Negative slack, bad constraints, congestion-sensitive paths", "Classify paths, tune implementation settings, rerun timing, summarize remaining critical paths"],
  ["PD closure: DRC", "Spacing, antenna, density, fill, or routing violations", "Parse DRC report, group violations, apply targeted repair or rerun selected PD stage"],
  ["PD closure: LVS", "Connectivity mismatch, missing device, pin mismatch, netlist/layout mismatch", "Compare layout and netlist evidence, isolate mismatch class, rerun extraction/LVS after fix"],
];

const loopSteps = [
  ["Analyze", "Read real reports, logs, dashboards, and artifacts from the failed run."],
  ["Classify", "Separate tool setup issues, input issues, generated-design issues, and closure-quality issues."],
  ["Repair", "Apply a bounded change: settings, constraints, testcase intent, collateral, or tool options."],
  ["Rerun", "Execute the relevant stage again with saved lineage and updated configuration."],
  ["Summarize", "Report what changed, what passed, and what still needs engineer review."],
];

export default function SelfRepairLoopsVerificationSynthesisPdPage() {
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
          Self-Repair Loops for Verification, Synthesis, and Physical Design Closure
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          The next step after AI-assisted generation is not blind automation. It is bounded self-repair: analyze evidence, make a targeted change, rerun the stage, and keep the engineer in control.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">What Is a Self-Repair Loop?</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A self-repair loop is a controlled closure pattern. The platform reads real run evidence, identifies likely causes, applies a bounded repair, reruns the relevant workflow stage, and summarizes the result.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            This is different from asking AI to guess. The loop is grounded in artifacts: coverage reports, synthesis logs, timing summaries, DRC reports, LVS output, generated LEF, and dashboard status.
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
          <h2 className="text-2xl font-bold text-white">The Repair Pattern</h2>
          <div className="mt-5 grid gap-3">
            {loopSteps.map(([step, body], index) => (
              <div key={step} className="grid gap-3 rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300 sm:grid-cols-[64px_0.35fr_1fr]">
                <div className="font-bold text-cyan-300">{String(index + 1).padStart(2, "0")}</div>
                <div className="font-semibold text-slate-100">{step}</div>
                <div>{body}</div>
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Loop</div>
            <div>Common Failure Evidence</div>
            <div>Self-Repair Action</div>
          </div>
          {closureRows.map(([loop, evidence, action]) => (
            <div key={loop} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{loop}</div>
              <div>{evidence}</div>
              <div>{action}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Example: Verification Closure</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A verification run may pass compilation but miss coverage targets or fail a subset of tests. A self-repair loop can analyze coverage gaps, identify missing stimulus or checkers, add testcase intent, rerun a bounded seed set, and emit a closure summary.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            The engineer still decides whether the new coverage is meaningful. The loop removes repeated manual setup and report chasing.
          </p>
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Example: Synthesis Closure</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A synthesis run may fail timing or produce a netlist that needs LEC review. A self-repair loop can classify whether the issue looks like constraints, hierarchy, retiming, tool option, or design-structure related, then rerun synthesis with a bounded change.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            The key is to keep every iteration visible: original settings, changed settings, timing result, LEC status, and final readiness.
          </p>
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Example: PD Closure with LEF, Timing, DRC, and LVS</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Physical design closure has multiple evidence streams. LEF checks catch abstract and pin issues. Timing checks show slack and path classes. DRC reports identify layout rule violations. LVS confirms layout and netlist equivalence.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            A self-repair loop should not hide these checks. It should group failures, apply targeted repair where appropriate, rerun the stage, and produce a clear closure dashboard for engineer review.
          </p>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Why ChipLoop Is Built for This</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            ChipLoop already keeps workflows, logs, artifacts, dashboards, Ask This Run, HEM, and product journeys connected. That connected evidence layer is what makes self-repair loops practical: repairs can be bounded, traceable, and reviewable instead of hidden inside a black box.
          </p>
        </section>
      </article>
    </main>
  );
}
