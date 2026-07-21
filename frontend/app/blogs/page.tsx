"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const articles = [
  {
    slug: "smart-context-tokenmaxxing",
    title: "Smart Context: Tokenmaxxing for Practical Silicon Workflows",
    summary: "How ChipLoop reduces unnecessary context, shows token estimates, and keeps Ask This Run and Ask this Project grounded in useful evidence.",
  },
  {
    slug: "hebbian-engineering-memory",
    title: "HEM: Automatic Engineering Memory for Connected Silicon Workflows",
    summary: "How Hebbian Engineering Memory helps ChipLoop continue successful runs into selected downstream workflows while preserving evidence and dashboards.",
  },
  {
    slug: "workflow-layer-ai-native-chip-design",
    title: "The Workflow Layer for AI-Native Chip Design",
    summary: "Why the durable value in AI chip design is workflow orchestration, not standalone prompt boxes.",
  },
  {
    slug: "semiconductor-tool-adoption-problem",
    title: "The Semiconductor Tool Adoption Problem",
    summary: "Why great EDA startups struggle to reach engineers, and how ChipLoop can become an integration layer.",
  },
  {
    slug: "end-to-end-ic-engineers-agentic-ai",
    title: "From Specialist Teams to End-to-End IC Engineers",
    summary: "How agentic AI expands engineering leverage without removing expert judgment.",
  },
  {
    slug: "top-five-chiploop-industry-problems",
    title: "Top 5 Industry Problems ChipLoop Addresses",
    summary: "A short priority view of the biggest industry workflow problems ChipLoop is positioned to solve.",
  },
  {
    slug: "future-end-to-end-ic-engineer",
    title: "The Future End-to-End IC Engineer",
    summary: "How agentic and generative AI can help engineers define, run, fix, and iterate across the full chip journey.",
  },
  {
    slug: "agentic-ai-future-chip-design",
    title: "Agentic AI and the Future of Chip Design",
    summary: "How AI assistance, copilots, agentic workflows, and traditional EDA reference flows can work together.",
  },
  {
    slug: "ask-this-run-engineering-review",
    title: "Why Ask This Run Changes Engineering Review",
    summary: "How run-grounded questions help engineers inspect logs, artifacts, warnings, and next steps without hunting through files.",
  },
  {
    slug: "navigating-loops-engineering-context",
    title: "Navigating Loops and Engineering Context",
    summary: "How ChipLoop helps teams define, configure, and run connected engineering loops, using the PWM reference journey as an example.",
  },
  {
    slug: "prompt-based-chip-design-to-chiploop",
    title: "From Prompt-Based Chip Design to ChipLoop",
    summary: "Why standalone prompts are not enough for real chip work, and how ChipLoop connects intent, tools, artifacts, checks, and handoffs.",
  },
];

export default function BlogsPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="blogs" showMarketplace showSettings={false} />
      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-4 py-10 sm:px-6">
        <div className="mx-auto max-w-[1440px]">
          <div className="max-w-4xl">
            <div className="text-xs font-semibold uppercase text-cyan-300">ChipLoop Blog</div>
            <h1 className="mt-3 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">Articles</h1>
            <p className="mt-4 text-lg leading-8 text-slate-300">
              Practical notes on agentic AI, connected chip workflows, HEM, Smart Context, product journeys, and semiconductor engineering productivity.
            </p>
          </div>

          <div className="mt-8 grid gap-4 md:grid-cols-2 xl:grid-cols-3">
            {articles.map((article) => (
              <button
                key={article.slug}
                type="button"
                onClick={() => router.push(`/blogs/${article.slug}`)}
                className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-left transition hover:-translate-y-0.5 hover:border-cyan-400 hover:bg-slate-900"
              >
                <div className="text-lg font-bold leading-snug text-white">{article.title}</div>
                <p className="mt-3 text-sm leading-6 text-slate-300">{article.summary}</p>
              </button>
            ))}
          </div>
        </div>
      </section>
    </main>
  );
}
