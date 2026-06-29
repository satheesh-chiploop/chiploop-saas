"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function EventsPage() {
  const router = useRouter();
  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="events" showMarketplace showSettings={false} />
      <section className="mx-auto max-w-6xl px-4 py-10 sm:px-6">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Events</div>
          <h1 className="mt-3 text-4xl font-extrabold tracking-tight sm:text-5xl">Webinars</h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Learn agentic chip design workflows, product journeys, Apps, Studio, implementation flows, and best practices.
          </p>
        </div>
        <div className="mt-8 grid gap-5 lg:grid-cols-[0.9fr_1.1fr]">
          <article className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-2xl font-bold text-cyan-300">Webinars</h2>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              Join focused walkthroughs of ChipLoop Apps, Studio, Products, connected Loops, generated artifacts, and dashboards once every two weeks.
            </p>
            <p className="mt-4 rounded-lg border border-cyan-900/70 bg-cyan-950/25 px-4 py-3 text-sm font-semibold text-cyan-100">
              Starts July 11, 2026 at 9:00 AM PST, then repeats every two weeks.
            </p>
            <button
              onClick={() => router.push("/webinar/register")}
              className="mt-5 rounded-lg bg-cyan-400 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-300"
            >
              View Webinars
            </button>
          </article>
          <article className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Events Blog</div>
            <h2 className="mt-2 text-2xl font-bold text-cyan-300">From Prompt-Based Chip Design to ChipLoop</h2>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              The first Events article explains why standalone prompts are not enough for real chip work, and how ChipLoop turns intent, tools, artifacts, checks, and handoffs into a connected workflow.
            </p>
            <button
              onClick={() => router.push("/events/blogs/prompt-based-chip-design-to-chiploop")}
              className="mt-5 rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
            >
              Read Article
            </button>
          </article>
        </div>
      </section>
    </main>
  );
}
