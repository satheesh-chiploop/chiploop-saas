"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["5 layers", "Agents, workflows, apps, products, and marketplace listings create a reusable silicon workflow stack."],
  ["40+ apps", "Prebuilt and private apps can turn repeatable engineering flows into one-click execution surfaces."],
  ["1 review path", "Admin-approved marketplace publication can separate private experimentation from shared reuse."],
];

const stack = [
  ["Agents", "Specialized AI/tool workers for RTL, verification, synthesis, validation, software, and review."],
  ["Workflows", "Connected sequences of agents with inputs, outputs, and handoff context."],
  ["Apps", "Packaged workflows that users can run, configure, and reuse."],
  ["Products", "Ordered chip journeys composed from apps and stages."],
  ["Marketplace", "Approved reusable capabilities that other users or teams can install."],
];

export default function MarketplaceReusableSiliconWorkflowsPage() {
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
          The Marketplace for Reusable Silicon Workflows
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Semiconductor teams should not rebuild the same environments, wrappers, checks, and handoff flows again and again. Reusable workflow packaging can change how chip tools are adopted.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Reuse Gap</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Many useful chip workflows start as internal scripts or one-off tool integrations. They solve real problems, but they are difficult for other teams to discover, install, configure, and trust.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            A marketplace model turns proven flows into reusable engineering products instead of fragile project-local knowledge.
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
          <h2 className="text-2xl font-bold text-white">The ChipLoop Stack</h2>
          <div className="mt-5 grid gap-3">
            {stack.map(([layer, body], index) => (
              <div key={layer} className="grid gap-3 rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300 sm:grid-cols-[64px_0.35fr_1fr]">
                <div className="font-bold text-cyan-300">{String(index + 1).padStart(2, "0")}</div>
                <div className="font-semibold text-slate-100">{layer}</div>
                <div>{body}</div>
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Why This Matters</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A reusable workflow marketplace can help teams adopt new tools faster, preserve engineering know-how, and reduce duplicated infrastructure work across companies and projects.
          </p>
        </section>
      </article>
    </main>
  );
}
