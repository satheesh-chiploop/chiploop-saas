"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const metrics = [
  ["0 public IP", "Private workflows should keep specs, RTL, reports, and run evidence inside the team's controlled environment."],
  ["3 access paths", "Web UI, SDK, and CLI let teams use the same workflow layer from interactive and automated environments."],
  ["1 policy layer", "Plans, credits, private apps, workflow access, and admin review can be controlled from one platform model."],
];

const rows = [
  ["IP protection", "Specs and generated files may move through unmanaged tools", "Private project context, private apps, and controlled workflow execution"],
  ["Team process", "Each team builds its own scripts and wrappers", "Reusable private workflows and apps that match the team's process"],
  ["Automation", "Browser work and automation live separately", "Same platform through UI, SDK, CLI, and CI-style integration"],
  ["Governance", "Hard to see who ran what and which outputs were generated", "Workflow IDs, logs, dashboards, and artifacts stay attached"],
];

export default function PrivateAiWorkflowsSiliconTeamsPage() {
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
          Why Silicon Teams Need Private AI Workflows
        </h1>
        <p className="mt-5 text-lg leading-8 text-slate-300">
          Chip design teams want AI leverage, but they also need IP control, repeatable process, private workflows, and clear evidence around every generated result.
        </p>

        <section className="mt-8 rounded-xl border border-slate-800 bg-slate-900/70 p-6">
          <h2 className="text-2xl font-bold text-white">AI Adoption Needs Trust</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            Semiconductor work contains valuable IP: requirements, RTL, verification plans, constraints, reports, timing data, validation notes, and product strategy. Teams will not adopt AI broadly if they cannot control where this context lives.
          </p>
          <p className="mt-3 leading-8 text-slate-300">
            Private AI workflows let teams use AI inside an engineering process rather than as an unmanaged side channel.
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

        <section className="mt-8 overflow-hidden rounded-xl border border-slate-800">
          <div className="grid grid-cols-3 bg-slate-900 p-3 text-xs font-bold uppercase tracking-wide text-cyan-200">
            <div>Need</div>
            <div>Traditional Risk</div>
            <div>ChipLoop Direction</div>
          </div>
          {rows.map(([need, risk, answer]) => (
            <div key={need} className="grid grid-cols-3 border-t border-slate-800 p-3 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">{need}</div>
              <div>{risk}</div>
              <div>{answer}</div>
            </div>
          ))}
        </section>

        <section className="mt-8 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-6">
          <h2 className="text-2xl font-bold text-white">Where ChipLoop Helps</h2>
          <p className="mt-3 leading-8 text-cyan-100">
            ChipLoop supports private apps, user-created workflows, SDK/CLI access, and product journeys. This lets teams bring AI into their own workflow without losing run history, artifacts, dashboards, or governance.
          </p>
        </section>
      </article>
    </main>
  );
}
