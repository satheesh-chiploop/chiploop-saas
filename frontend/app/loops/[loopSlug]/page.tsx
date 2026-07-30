"use client";

import { useMemo, useState } from "react";
import { notFound, useParams, useRouter } from "next/navigation";
import { FaArrowRight, FaCheck, FaChevronDown, FaFileUpload, FaMicrochip, FaPlay } from "react-icons/fa";
import TopNav from "@/components/TopNav";
import { loopOverviews } from "@/lib/loopOverview";
import { loopCatalogMetrics } from "@/lib/platformMetrics";

type DetailView = "workflow" | "apps" | "agents";
const metricDisplay = [
  { key: "agents", label: "Agents", color: "bg-cyan-300" },
  { key: "workflows", label: "Workflows", color: "bg-violet-400" },
  { key: "apps", label: "Apps", color: "bg-emerald-300" },
  { key: "productJourneys", label: "Product journeys", color: "bg-pink-400" },
  { key: "referenceJourneys", label: "Reference journeys", color: "bg-amber-300" },
] as const;
const miniRvBoardSweep = [
  { board: "Lattice iCEBreaker", fmax: 0, status: "Does not fit", utilization: 105.53 },
  { board: "Lattice UPduino v3", fmax: 0, status: "Does not fit", utilization: 105.53 },
  { board: "Lattice iCEstick", fmax: 0, status: "Does not fit", utilization: 435.313 },
  { board: "Lattice iCE40 HX8K Breakout", fmax: 32.377, status: "Target met", utilization: 72.552 },
  { board: "Lattice Colorlight 5A-75B ECP5-25F", fmax: 51.01, status: "Target met", utilization: 16.753 },
  { board: "Lattice ULX3S ECP5-45F", fmax: 52.187, status: "Target met", utilization: 9.28 },
  { board: "Lattice OrangeCrab ECP5-85F", fmax: 51.578, status: "Target met", utilization: 4.865 },
  { board: "Gowin Tang Nano 9K", fmax: 0, status: "Does not fit", utilization: 156.771 },
  { board: "Gowin Tang Nano 20K", fmax: 50.984, status: "Target met", utilization: 66.04 },
  { board: "Gowin Tang Primer 20K", fmax: 50.256, status: "Target met", utilization: 66.04 },
  { board: "Lattice Certus-NX Versa", fmax: 88.652, status: "Target met", utilization: 8.302 },
  { board: "Lattice CrossLink-NX Evaluation", fmax: 96.488, status: "Target met", utilization: 8.302 },
];
const miniRvChartMax = 100;
export default function LoopOverviewPage() {
  const params = useParams<{ loopSlug: string }>();
  const router = useRouter();
  const [detailView, setDetailView] = useState<DetailView>("workflow");
  const loop = useMemo(() => loopOverviews[params.loopSlug], [params.loopSlug]);
  if (!loop) notFound();
  const catalog = loopCatalogMetrics[params.loopSlug];
  const metrics = catalog ? metricDisplay.map((metric) => ({ ...metric, value: catalog[metric.key] })) : [];

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="loops" showMarketplace showSettings={false} />
      <section className="border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.12),transparent_36%),linear-gradient(180deg,#020617_0%,#0f172a_64%,#020617_100%)] px-4 py-10 sm:px-6 sm:py-14">
        <div className="mx-auto max-w-6xl">
          <button onClick={() => router.push("/loops")} className="text-sm font-semibold text-slate-400 hover:text-cyan-200">&larr; All design loops</button>
          <div className="mt-8 grid items-center gap-8 lg:grid-cols-[1.2fr_0.8fr]">
            <div>
              <p className={`text-xs font-bold uppercase tracking-[0.18em] ${loop.accentText}`}>{loop.eyebrow}</p>
              <h1 className="mt-3 max-w-4xl text-4xl font-extrabold leading-tight sm:text-5xl">{loop.promise}</h1>
              <p className="mt-5 max-w-3xl text-lg leading-8 text-slate-300">{loop.description}</p>
              <div className="mt-7 flex flex-wrap gap-3">
                <button onClick={() => router.push(loop.starts[0].href)} className="inline-flex items-center gap-2 rounded-lg bg-cyan-400 px-5 py-3 text-sm font-extrabold text-slate-950 hover:bg-cyan-300">
                  <FaPlay className="h-3 w-3" aria-hidden="true" /> {loop.starts[0].label}
                </button>
                <button onClick={() => document.getElementById("choose-start")?.scrollIntoView({ behavior: "smooth" })} className={`rounded-lg border ${loop.accentBorder} px-5 py-3 text-sm font-bold hover:bg-slate-900`}>See ways to start</button>
              </div>
            </div>
            <div className={`rounded-2xl border ${loop.accentBorder} bg-slate-950/75 p-5 shadow-2xl shadow-slate-950/40 sm:p-6`}>
              <div className="flex items-center gap-3">
                <span className={`flex h-10 w-10 items-center justify-center rounded-xl ${loop.accent} text-slate-950`}><FaFileUpload aria-hidden="true" /></span>
                <div><div className="text-xs font-bold uppercase text-slate-500">What you provide</div><div className="mt-1 font-bold">Just the engineering intent</div></div>
              </div>
              <div className="mt-5 space-y-3">
                {loop.inputs.map((input) => <div key={input} className="flex items-start gap-3 rounded-lg bg-slate-900/80 px-4 py-3 text-sm text-slate-300"><FaCheck className={`mt-0.5 h-3.5 w-3.5 shrink-0 ${loop.accentText}`} />{input}</div>)}
              </div>
              <p className="mt-4 text-xs leading-5 text-slate-500">ChipLoop handles workflow orchestration, specialist agents, tool settings, retries, and evidence tracking.</p>
            </div>
          </div>
        </div>
      </section>


      <section className="border-b border-slate-800 bg-slate-900/25 px-4 py-8 sm:px-6">
        <div className="mx-auto max-w-6xl">
          <div className="flex flex-wrap items-end justify-between gap-3">
            <div><p className={`text-xs font-bold uppercase tracking-[0.18em] ${loop.accentText}`}>Loop at a glance</p><h2 className="mt-2 text-2xl font-extrabold">Connected capability, kept simple</h2></div>
            <p className="text-xs text-slate-500">Current prebuilt catalog snapshot</p>
          </div>
          <div className="mt-6 grid grid-cols-2 gap-3 sm:grid-cols-5">
            {metrics.map((metric) => (
              <div key={metric.label} className="rounded-xl border border-slate-800 bg-slate-950/75 p-4">
                <div className="flex items-end justify-between gap-2"><span className="text-2xl font-extrabold text-white">{metric.value}</span><span className={`h-2.5 w-2.5 rounded-full ${metric.color}`} /></div>
                <div className="mt-2 text-xs font-semibold text-slate-400">{metric.label}</div>
              </div>
            ))}
          </div>
        </div>
      </section>
      <section className="px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-6xl">
          <div className="text-center"><p className={`text-xs font-bold uppercase tracking-[0.18em] ${loop.accentText}`}>What happens</p><h2 className="mt-2 text-3xl font-extrabold">A clear path from input to result</h2></div>
          <div className="mt-7 overflow-x-auto pb-2">
            <div className="mx-auto flex min-w-[720px] max-w-5xl items-stretch">
              {loop.stages.map((stage, index) => (
                <div key={stage.label} className="flex min-w-0 flex-1 items-center">
                  <div className="h-full flex-1 rounded-xl border border-slate-800 bg-slate-900/70 p-4"><div className={`text-xs font-extrabold ${loop.accentText}`}>{String(index + 1).padStart(2, "0")}</div><h3 className="mt-2 font-extrabold">{stage.label}</h3><p className="mt-2 text-xs leading-5 text-slate-400">{stage.detail}</p></div>
                  {index < loop.stages.length - 1 ? <FaArrowRight className={`mx-2 h-3 w-3 shrink-0 ${loop.accentText}`} /> : null}
                </div>
              ))}
            </div>
          </div>

          {params.loopSlug === "fpga" ? (
            <div className="mt-8 rounded-xl border border-lime-300/35 bg-slate-900/70 p-5 sm:p-6">
              <div className="flex flex-wrap items-start justify-between gap-3">
                <div>
                  <p className="text-xs font-bold uppercase tracking-[0.18em] text-lime-200">MiniRV FPGA Explorer</p>
                  <h2 className="mt-2 text-2xl font-extrabold">12-board reference comparison</h2>
                  <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-400">Completed reference run at a 25 MHz target using one baseline seed per board. Eight targets met timing; four smaller targets did not fit the design.</p>
                </div>
                <button onClick={() => router.push("/apps/fpga-target-explorer?reference=minirv")} className="rounded-lg bg-lime-300 px-4 py-2 text-sm font-extrabold text-slate-950 hover:bg-lime-200">Run MiniRV Explorer</button>
              </div>
              <div className="mt-5 flex flex-wrap gap-2 text-xs">
                <span className="rounded-full border border-lime-300/35 bg-lime-300/10 px-3 py-1.5 font-bold text-lime-200">Best overall: CrossLink-NX</span>
                <span className="rounded-full border border-cyan-300/30 bg-cyan-300/10 px-3 py-1.5 font-bold text-cyan-200">Best performance: 96.488 MHz</span>
                <span className="rounded-full border border-amber-300/30 bg-amber-300/10 px-3 py-1.5 font-bold text-amber-200">Best low cost: iCE40 HX8K</span>
                <span className="rounded-full border border-violet-300/30 bg-violet-300/10 px-3 py-1.5 font-bold text-violet-200">Best growth: OrangeCrab ECP5-85F</span>
              </div>
              <div className="mt-6 space-y-3">
                {miniRvBoardSweep.map((result) => (
                  <div key={result.board} className="grid gap-1 text-xs sm:grid-cols-[260px_1fr_150px] sm:items-center sm:gap-3">
                    <span className="truncate font-bold text-slate-300" title={result.board}>{result.board}</span>
                    <div className="relative h-6 overflow-hidden rounded-md bg-slate-950">
                      {result.fmax > 0 ? <div className="absolute inset-y-0 left-0 bg-lime-300/75" style={{ width: `${(result.fmax / miniRvChartMax) * 100}%` }} /> : null}
                      <div className="absolute inset-y-0 border-l border-dashed border-amber-300/80" style={{ left: "25%" }} title="25 MHz target" />
                    </div>
                    <span className={`text-right font-extrabold ${result.fmax > 0 ? "text-white" : "text-rose-300"}`}>{result.fmax > 0 ? `${result.fmax} MHz` : `Does not fit (${result.utilization}%)`}</span>
                  </div>
                ))}
              </div>
              <div className="mt-4 flex items-center justify-between text-[11px] text-slate-500"><span>0 MHz</span><span className="text-amber-200">Target 25 MHz</span><span>100 MHz</span></div>
            </div>
          ) : null}          <div className="mt-8 grid gap-5 lg:grid-cols-[0.9fr_1.1fr]">
            <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5">
              <div className="flex items-center gap-3"><FaMicrochip className={`h-5 w-5 ${loop.accentText}`} /><h2 className="text-xl font-extrabold">What you receive</h2></div>
              <div className="mt-5 space-y-3">{loop.outcomes.map((outcome) => <div key={outcome} className="flex items-center gap-3 text-sm text-slate-300"><span className={`h-2 w-2 rounded-full ${loop.accent}`} />{outcome}</div>)}</div>
            </div>
            <button onClick={() => router.push(loop.reference.href)} className={`group rounded-xl border ${loop.accentBorder} bg-slate-900/70 p-5 text-left hover:bg-slate-900`}>
              <div className="flex flex-wrap items-start justify-between gap-3"><div><div className={`text-xs font-bold uppercase ${loop.accentText}`}>Reference journey</div><h2 className="mt-2 text-xl font-extrabold">{loop.reference.title}</h2><p className="mt-2 text-sm leading-6 text-slate-400">{loop.reference.description}</p></div><span className="text-sm font-bold text-slate-300 group-hover:text-white">View journey &rarr;</span></div>
              <div className="mt-5 flex flex-wrap items-center gap-2">{loop.reference.results.map((result, index) => <div key={result.label} className="flex items-center gap-2"><span className={`rounded-full border ${loop.accentBorder} bg-slate-950/80 px-3 py-2 text-xs font-bold text-slate-200`}>{result.label}</span>{index < loop.reference.results.length - 1 ? <FaArrowRight className={`h-3 w-3 shrink-0 ${loop.accentText}`} aria-hidden="true" /> : null}</div>)}</div>
            </button>
          </div>
        </div>
      </section>

      <section id="choose-start" className="scroll-mt-24 border-y border-slate-800 bg-slate-900/25 px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-6xl">
          <div className="text-center"><p className={`text-xs font-bold uppercase tracking-[0.18em] ${loop.accentText}`}>Choose where to begin</p><h2 className="mt-2 text-3xl font-extrabold">Start with what you have</h2></div>
          <div className="mt-7 grid gap-4 md:grid-cols-3">{loop.starts.map((start) => <button key={start.title} onClick={() => router.push(start.href)} className="group rounded-xl border border-slate-800 bg-slate-950/70 p-5 text-left hover:-translate-y-0.5 hover:border-cyan-400/60"><h3 className="text-lg font-extrabold">{start.title}</h3><p className="mt-3 min-h-12 text-sm leading-6 text-slate-400">{start.body}</p><div className={`mt-5 inline-flex items-center gap-2 text-sm font-bold ${loop.accentText}`}>{start.label}<FaArrowRight className="h-3 w-3 transition group-hover:translate-x-1" /></div></button>)}</div>
        </div>
      </section>



      <section className="px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-6xl">
          <details className="group rounded-xl border border-slate-800 bg-slate-900/55">
            <summary className="flex cursor-pointer list-none items-center justify-between gap-4 px-5 py-5 sm:px-6"><div><h2 className="text-lg font-extrabold">See how this Loop works</h2><p className="mt-1 text-sm text-slate-500">Optional details about the workflow, apps, and agents.</p></div><FaChevronDown className="h-4 w-4 text-slate-400 transition group-open:rotate-180" /></summary>
            <div className="border-t border-slate-800 p-5 sm:p-6">
              <div className="flex flex-wrap gap-2" role="tablist">
                {(["workflow", "apps", "agents"] as DetailView[]).map((view) => <button key={view} role="tab" aria-selected={detailView === view} onClick={() => setDetailView(view)} className={`rounded-lg px-4 py-2 text-sm font-bold capitalize ${detailView === view ? `${loop.accent} text-slate-950` : "border border-slate-700 text-slate-300"}`}>{view}</button>)}
              </div>
              {detailView === "workflow" ? <div className="mt-5 rounded-xl border border-slate-800 bg-slate-950/70 p-5"><h3 className="font-extrabold">The workflow</h3><p className="mt-3 max-w-3xl text-sm leading-7 text-slate-300">{loop.workflow}</p><div className="mt-5 flex flex-wrap items-center gap-2">{loop.stages.map((stage, index) => <div key={stage.label} className="flex items-center gap-2"><span className="rounded-full border border-slate-700 bg-slate-900 px-3 py-1.5 text-xs font-bold">{stage.label}</span>{index < loop.stages.length - 1 ? <span className="text-slate-600">&rarr;</span> : null}</div>)}</div></div> : null}
              {detailView === "apps" ? <div className="mt-5 grid gap-3 md:grid-cols-3">{loop.apps.map((app) => <button key={app.name} onClick={() => router.push(app.href)} className="rounded-xl border border-slate-800 bg-slate-950/70 p-4 text-left hover:border-cyan-400/50"><h3 className="font-extrabold">{app.name}</h3><p className="mt-2 text-sm leading-6 text-slate-400">{app.description}</p><div className={`mt-3 text-xs font-bold uppercase ${loop.accentText}`}>Open app &rarr;</div></button>)}</div> : null}
              {detailView === "agents" ? <div className="mt-5 grid gap-3 md:grid-cols-3">{loop.agentGroups.map((agent) => <div key={agent.name} className="rounded-xl border border-slate-800 bg-slate-950/70 p-4"><h3 className="font-extrabold">{agent.name}</h3><p className="mt-2 text-sm leading-6 text-slate-400">{agent.description}</p></div>)}</div> : null}
            </div>
          </details>
        </div>
      </section>
    </main>
  );
}
