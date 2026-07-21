"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

export default function EventsPage() {
  const router = useRouter();
  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="events" showMarketplace showSettings={false} />
      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1440px]">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase text-cyan-300">Events</div>
          <h1 className="mt-3 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">Webinars</h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Learn agentic chip design workflows, product journeys, Apps, Studio, implementation flows, and best practices.
          </p>
        </div>
        <div className="mt-8 grid gap-5 lg:grid-cols-2">
          <article className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-3xl font-extrabold leading-tight text-white sm:text-4xl">Webinars</h2>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              Join focused walkthroughs of ChipLoop Apps, Studio, Products, connected Loops, generated artifacts, and dashboards once every two weeks.
            </p>
            <p className="mt-4 rounded-lg border border-slate-700 bg-slate-950/60 px-4 py-3 text-sm font-semibold text-slate-200">
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
            <div className="text-xs font-semibold uppercase text-slate-400">Articles</div>
            <h2 className="mt-2 text-3xl font-extrabold leading-tight text-white sm:text-4xl">Read the ChipLoop Blog</h2>
            <p className="mt-3 text-sm leading-6 text-slate-300">
              Product notes, engineering articles, HEM, Smart Context, agentic AI, and connected silicon workflow thinking now live in a separate Blogs section.
            </p>
            <button
              type="button"
              onClick={() => router.push("/blogs")}
              className="mt-5 rounded-lg border border-cyan-700 px-5 py-3 text-sm font-bold text-cyan-100 hover:bg-cyan-950/40"
            >
              Open Blogs
            </button>
          </article>
        </div>
        </div>
      </section>
    </main>
  );
}
