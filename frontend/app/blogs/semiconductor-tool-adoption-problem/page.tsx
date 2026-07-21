"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function SemiconductorToolAdoptionProblemPage() {
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
          The Semiconductor Tool Adoption Problem
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Many promising EDA and AI semiconductor startups fail to scale because getting into a real engineering workflow is slow, expensive, and highly custom.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Bottleneck</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A startup tool may solve one painful problem, but customers still ask: how does it connect to our specs, scripts, reports, design data, reviews, and signoff process?
          </p>
        </section>

        <section className="mt-8 grid gap-4 md:grid-cols-2">
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
            <h3 className="text-lg font-bold text-white">Current Adoption Path</h3>
            <ul className="mt-4 space-y-3 text-sm leading-6 text-slate-300">
              <li>- Custom pilot with one team</li>
              <li>- Manual data movement</li>
              <li>- Separate dashboard or report</li>
              <li>- Integration scripts per customer</li>
              <li>- Hard to prove end-to-end value</li>
            </ul>
          </div>
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
            <h3 className="text-lg font-bold text-white">ChipLoop Adoption Path</h3>
            <ul className="mt-4 space-y-3 text-sm leading-6 text-slate-300">
              <li>- Tool becomes an app, agent, or workflow stage</li>
              <li>- Inputs and outputs attach to a run</li>
              <li>- Artifacts are preserved and downloadable</li>
              <li>- Ask This Run reviews tool evidence</li>
              <li>- Value is shown in end-to-end context</li>
            </ul>
          </div>
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why ChipLoop Is Useful for Tool Startups</h2>
          <p className="leading-8">
            ChipLoop can serve as a distribution and integration layer. A specialized tool does not need to become a complete chip design platform. It can plug into ChipLoop as a loop step, expose inputs and outputs, and participate in a larger engineering journey.
          </p>
          <p className="leading-8">
            That matters because semiconductor buyers care about workflow fit. They want to see how a tool improves an actual design path, not only how it performs on an isolated demo.
          </p>
        </section>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">Platform Opportunity</h2>
          <div className="mt-5 grid gap-3 text-center text-sm font-semibold text-slate-100 sm:grid-cols-4">
            {["Startup Tool", "ChipLoop Stage", "Run Evidence", "Customer Workflow"].map((step) => (
              <div key={step} className="rounded-lg border border-cyan-900/70 bg-slate-950/60 p-4">
                {step}
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 space-y-4 text-slate-300">
          <h2 className="text-2xl font-bold text-white">Why It Matters</h2>
          <p className="leading-8">
            If ChipLoop becomes the place where emerging semiconductor tools are tried, connected, reviewed, and reused, it can create leverage beyond its own first-party apps. That is an ecosystem opportunity, not just a workflow improvement.
          </p>
        </section>
      </article>
    </main>
  );
}
