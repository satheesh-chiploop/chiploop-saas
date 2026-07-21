"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function HebbianEngineeringMemoryPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="blogs" showMarketplace showSettings={false} />
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
          HEM: Automatic Engineering Memory for Connected Silicon Workflows
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Hebbian Engineering Memory helps ChipLoop move from one successful workflow to the next selected engineering step while keeping evidence, dashboards, and handoffs connected.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Core Idea</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            HEM turns a completed run into a controlled continuation. If Arch2RTL passes, ChipLoop can continue to DQA, verification, synthesis, or tapeout. If System RTL passes, ChipLoop can continue toward implementation or product-demo stages.
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-3">
          {[
            ["Pass", "Wait for the current workflow to complete successfully."],
            ["Select", "Use the enabled HEM policy and stage toggles to choose the next step."],
            ["Continue", "Start the next workflow with upstream IDs, logs, artifacts, and dashboard links preserved."],
          ].map(([title, body]) => (
            <div key={title} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <h3 className="text-lg font-bold text-white">{title}</h3>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why HEM Matters</h2>
          <p className="leading-8">
            Silicon work is not a single prompt or a single tool run. A useful result must be checked, handed off, implemented, verified, and reviewed. HEM helps automate that transition without hiding the engineering evidence.
          </p>
          <p className="leading-8">
            The user stays in control. HEM is disabled by default. When enabled, the user can choose fixed or adaptive policy and can turn individual downstream stages on or off before the run starts.
          </p>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Flow</div>
            <div>Default Continuation</div>
            <div>User Control</div>
          </div>
          {[
            ["Digital HEM", "Arch2RTL -> DQA -> Verification -> Synthesis -> Tapeout", "Enable or disable DQA, Verification, Synthesis, and Tapeout."],
            ["System HEM: Product Demo", "System RTL -> DQA -> Sim -> Firmware -> Software -> Co-sim/Validation -> Product Demo", "Choose Product Demo goal and allowed stages."],
            ["System HEM: Implementation", "System RTL -> DQA -> Synthesis -> System PD", "Choose Implementation goal and allowed stages."],
          ].map(([flow, continuation, control]) => (
            <div key={flow} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{flow}</div>
              <div>{continuation}</div>
              <div>{control}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Fixed and Adaptive HEM</h2>
          <p className="mt-3 leading-8 text-slate-300">
            Fixed HEM follows the built-in continuation policy. Adaptive HEM starts from the same policy and records successful transitions for future learning. In simple form, the update follows:
          </p>
          <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950 p-4 text-center font-mono text-lg text-cyan-100">
            delta_w = eta * x_i * x_j
          </div>
          <p className="mt-3 text-sm leading-6 text-slate-400">
            Here, eta is the learning rate and x_i/x_j represent the activity of two connected workflow stages. The practical goal is simple: successful engineering transitions become stronger signals over time.
          </p>
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">What the Engineer Sees</h2>
          <p className="leading-8">
            After HEM runs, the root workflow shows a HEM Run Summary table. Each child workflow has its own workflow ID, real status from Supabase, and an Open Dashboard link that opens in a new tab.
          </p>
          <p className="leading-8">
            This makes HEM feel like a compact product journey: the user can review each stage dashboard, inspect artifacts, download ZIP files, and use Ask This Run without losing the original run context.
          </p>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">The Bigger Direction</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            HEM is a step toward self-regulated silicon workflows: systems that can run the next appropriate check, preserve what happened, and learn which transitions worked, while still leaving engineers in control of policy, evidence, and signoff decisions.
          </p>
        </section>
      </article>
    </main>
  );
}
