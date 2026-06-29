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
            <h2 className="mt-2 text-2xl font-bold text-cyan-300">Latest Articles</h2>
            <div className="mt-4 space-y-4">
              <button
                type="button"
                onClick={() => router.push("/events/blogs/workflow-layer-ai-native-chip-design")}
                className="block w-full rounded-lg border border-cyan-900/60 bg-cyan-950/20 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">The Workflow Layer for AI-Native Chip Design</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  Why the durable value in AI chip design is workflow orchestration, not standalone prompt boxes.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/semiconductor-tool-adoption-problem")}
                className="block w-full rounded-lg border border-cyan-900/60 bg-cyan-950/20 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">The Semiconductor Tool Adoption Problem</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  Why great EDA startups struggle to reach engineers, and how ChipLoop can become an integration layer.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/end-to-end-ic-engineers-agentic-ai")}
                className="block w-full rounded-lg border border-cyan-900/60 bg-cyan-950/20 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">From Specialist Teams to End-to-End IC Engineers</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  How agentic AI expands engineering leverage without removing expert judgment.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/top-five-chiploop-industry-problems")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">Top 5 Industry Problems ChipLoop Addresses</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  A short priority view of the biggest industry workflow problems ChipLoop is positioned to solve.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/future-end-to-end-ic-engineer")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">The Future End-to-End IC Engineer</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  How agentic and generative AI can help engineers define, run, fix, and iterate across the full chip journey, and how ChipLoop makes startup tools easier to integrate.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/agentic-ai-future-chip-design")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">Agentic AI and the Future of Chip Design</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  How AI assistance, copilots, agentic workflows, and traditional EDA reference flows can work together.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/ask-this-run-engineering-review")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">Why Ask This Run Changes Engineering Review</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  How run-grounded questions help engineers inspect logs, artifacts, warnings, and next steps without hunting through files.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/navigating-loops-engineering-context")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">Navigating Loops and Engineering Context</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  How ChipLoop helps teams define, configure, and run connected engineering loops, using the PWM reference journey as an example.
                </p>
              </button>
              <button
                type="button"
                onClick={() => router.push("/events/blogs/prompt-based-chip-design-to-chiploop")}
                className="block w-full rounded-lg border border-slate-800 bg-slate-950/40 p-4 text-left hover:border-cyan-400"
              >
                <div className="text-sm font-bold text-cyan-100">From Prompt-Based Chip Design to ChipLoop</div>
                <p className="mt-2 text-sm leading-6 text-slate-300">
                  Why standalone prompts are not enough for real chip work, and how ChipLoop connects intent, tools, artifacts, checks, and handoffs.
                </p>
              </button>
            </div>
          </article>
        </div>
      </section>
    </main>
  );
}
