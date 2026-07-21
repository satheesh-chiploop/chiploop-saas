"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function NavigatingLoopsEngineeringContextPage() {
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
          Navigating Loops and Engineering Context
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Chip design teams do not just need a generated file. They need a way to define intent, configure the right engineering path, run it, inspect the evidence, and then move into the next loop without losing context.
        </p>

        <div className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-sm leading-7 text-slate-300">
          A loop is a repeatable engineering path: define what you want, configure the run, execute it, inspect results, and carry the context forward.
        </div>

        <div className="mt-10 space-y-9 text-slate-300">
          <section>
            <h2 className="text-2xl font-bold text-white">Why Navigation Matters</h2>
            <p className="mt-3 leading-8">
              Modern chip work spans architecture, RTL, verification, synthesis, physical design, embedded software, validation, and product-level decisions. Each domain has its own inputs, tools, reports, and review language. The hard part is not only generating an artifact; it is knowing where that artifact belongs and what should happen next.
            </p>
            <p className="mt-3 leading-8">
              Traditional flows often force engineers to navigate that context manually. A spec becomes a document, then RTL files, then testbenches, then logs, then implementation reports. The connections between those steps are easy to lose, especially when a run fails or a requirement changes.
            </p>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Define, Configure, and Run</h2>
            <p className="mt-3 leading-8">
              ChipLoop organizes engineering work around a simple pattern: define, configure, and run. Define captures the design intent or reference journey. Configure selects the options, scope, and loop behavior. Run executes the workflow and preserves the evidence.
            </p>
            <p className="mt-3 leading-8">
              This matters because chip design decisions are contextual. A verification run means something different if it follows a new RTL generation, a synthesis failure, or a product journey handoff. ChipLoop keeps those relationships visible so users can move between loops with less manual reconstruction.
            </p>
          </section>

          <section className="grid gap-4 md:grid-cols-3">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Define</h3>
              <p className="mt-3 text-sm leading-6">
                Start with a spec, app, product stage, or reference journey. The goal is to establish the engineering intent and the expected handoff.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Configure</h3>
              <p className="mt-3 text-sm leading-6">
                Choose the loop, settings, run options, closure behavior, and any uploaded context that should shape the workflow.
              </p>
            </div>
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">Run</h3>
              <p className="mt-3 text-sm leading-6">
                Execute the workflow, inspect dashboards and artifacts, ask questions about the run, and continue into the next loop.
              </p>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Example: PWM Reference Journey</h2>
            <p className="mt-3 leading-8">
              The PWM reference journey is a good example because it is simple enough to understand quickly, but rich enough to show how context moves. A user begins with a PWM controller intent: registers, duty cycle behavior, period control, enable behavior, interrupt/status expectations, and handoff needs.
            </p>
            <p className="mt-3 leading-8">
              In a prompt-only flow, the user might ask for PWM RTL and then manually decide what to do with it. In ChipLoop, the journey can guide the user through the loop: generate or inspect RTL, review generated files, check constraints or verification evidence, download artifacts, and use Ask This Run to understand what was produced.
            </p>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-2xl font-bold text-white">How Context Carries Forward</h2>
            <div className="mt-5 space-y-4 text-sm leading-7">
              <p>
                The PWM journey starts as design intent, but it does not stop there. The RTL loop creates implementation artifacts. The verification loop can reason about expected behavior such as duty-cycle updates, reset behavior, register writes, and interrupt status. The synthesis or implementation loop can consume the RTL and constraints. A product journey can package the flow as a repeatable stage.
              </p>
              <p>
                ChipLoop helps because each loop does not have to start from scratch. The platform keeps run metadata, logs, generated artifacts, dashboards, and summaries together. That gives engineers a clearer path from one decision to the next.
              </p>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">Traditional Navigation vs ChipLoop Navigation</h2>
            <div className="mt-5 grid gap-4 md:grid-cols-2">
              <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
                <h3 className="text-lg font-bold text-white">Traditional</h3>
                <ul className="mt-4 space-y-3 text-sm leading-6">
                  <li>- Engineers manually track which files belong to which step</li>
                  <li>- Reports and logs live away from the original design intent</li>
                  <li>- Moving from RTL to verification or synthesis requires hand assembly</li>
                  <li>- Failed runs require manual triage across scattered artifacts</li>
                </ul>
              </div>
              <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
                <h3 className="text-lg font-bold text-white">ChipLoop</h3>
                <ul className="mt-4 space-y-3 text-sm leading-6">
                  <li>- Apps and reference journeys guide users into the right loop</li>
                  <li>- Configuration stays attached to the workflow run</li>
                  <li>- Artifacts, logs, dashboards, and Ask This Run stay connected</li>
                  <li>- Users can continue from define to configure to run, then into the next loop</li>
                </ul>
              </div>
            </div>
          </section>

          <section>
            <h2 className="text-2xl font-bold text-white">The Practical Benefit</h2>
            <p className="mt-3 leading-8">
              Engineering context is what makes chip work trustworthy. ChipLoop helps users navigate that context by turning workflows into connected loops instead of disconnected tasks. The PWM reference journey shows the pattern: start with a known design goal, configure the run, execute it, inspect real evidence, and carry the results forward.
            </p>
            <p className="mt-3 leading-8">
              That is the value of define, configure, and run. It gives teams a practical way to move from intent to evidence while keeping the path visible.
            </p>
          </section>
        </div>
      </article>
    </main>
  );
}
