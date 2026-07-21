"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["3 steps", "Define the product intent, configure stages and inputs, then run connected workflows with preserved evidence."],
  ["5-10x", "More repeatable reuse when common engineering paths are packaged as product journeys instead of rebuilt from scratch."],
  ["1 view", "Product-level history, stages, logs, dashboards, workflow IDs, and results stay connected for review."],
];

const comparisonRows = [
  ["Starting point", "A requirement document, email thread, or script folder", "A product journey with product type, starting point, stages, and reference path"],
  ["Configuration", "Manual tool setup and repeated input collection", "Stage-level settings saved with the product and rendered from real workflow contracts"],
  ["Execution", "Separate workflow launches and manual tracking", "Run selected product stages in sequence with lineage and logs"],
  ["Review", "Engineers hunt through folders and reports", "Dashboards, ZIPs, Ask This Run, and product run history remain linked"],
  ["Reuse", "Knowledge stays with scripts or individual engineers", "Products and private apps can be reused, evolved, and marketplace-ready"],
];

const defineConfigureRun = [
  ["Define", "Capture what the chip journey is: product type, goal, starting point, reference journey, and expected outcome."],
  ["Configure", "Choose stages, add apps, fill real workflow inputs, select options, and save settings with the product."],
  ["Run", "Execute stages, watch logs, open dashboards, inspect artifacts, ask questions, and continue from failures or next steps."],
];

export default function ProductJourneyDefineConfigureRunPage() {
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
          Product Journeys: Define, Configure, and Run Changes the Chip Design Landscape
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Chip design has traditionally been organized around tools and teams. Product journeys organize the work around the outcome: a chip block, subsystem, demo, or product-ready package.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">The Core Shift</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            A product journey turns scattered engineering steps into a connected path. Instead of asking users to remember which app, workflow, input, report, and dashboard comes next, ChipLoop keeps the product stages together.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            This is important because real chip work is not a single generation step. It is define, configure, run, inspect, fix, and continue. Product journeys make that pattern visible and repeatable.
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
          <h2 className="text-2xl font-bold text-white">Define, Configure, Run</h2>
          <div className="mt-5 grid gap-4 md:grid-cols-3">
            {defineConfigureRun.map(([step, body], index) => (
              <div key={step} className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm font-bold text-cyan-300">{String(index + 1).padStart(2, "0")}</div>
                <h3 className="mt-3 text-xl font-bold text-white">{step}</h3>
                <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
              </div>
            ))}
          </div>
        </section>

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Area</div>
            <div>Traditional Loop</div>
            <div>Product Journey</div>
          </div>
          {comparisonRows.map(([area, traditional, product]) => (
            <div key={area} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{area}</div>
              <div>{traditional}</div>
              <div>{product}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Why This Changes the Landscape</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Product journeys let small teams work with a product mindset from the beginning. The same platform can capture intent, configure stages, run apps, preserve evidence, inspect failures, and package results. That turns chip work from a collection of disconnected tool runs into a repeatable product development system.
          </p>
        </section>
      </article>
    </main>
  );
}
