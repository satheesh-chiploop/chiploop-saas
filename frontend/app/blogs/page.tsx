"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const articles = [
  {
    slug: "smart-context-tokenmaxxing",
    title: "Smart Context: Tokenmaxxing for Practical Silicon Workflows",
    summary: "How ChipLoop reduces unnecessary context, shows token estimates, and keeps Ask This Run and Ask this Project grounded in useful evidence.",
    tag: "Smart Context",
    accent: "from-cyan-400 to-emerald-300",
  },
  {
    slug: "hebbian-engineering-memory",
    title: "HEM: Automatic Engineering Memory for Connected Silicon Workflows",
    summary: "How Hebbian Engineering Memory helps ChipLoop continue successful runs into selected downstream workflows while preserving evidence and dashboards.",
    tag: "HEM",
    accent: "from-amber-300 to-cyan-300",
  },
  {
    slug: "workflow-layer-ai-native-chip-design",
    title: "The Workflow Layer for AI-Native Chip Design",
    summary: "Why the durable value in AI chip design is workflow orchestration, not standalone prompt boxes.",
    tag: "Platform",
    accent: "from-violet-300 to-cyan-300",
  },
  {
    slug: "semiconductor-tool-adoption-problem",
    title: "The Semiconductor Tool Adoption Problem",
    summary: "Why great EDA startups struggle to reach engineers, and how ChipLoop can become an integration layer.",
    tag: "Industry",
    accent: "from-rose-300 to-amber-300",
  },
  {
    slug: "end-to-end-ic-engineers-agentic-ai",
    title: "From Specialist Teams to End-to-End IC Engineers",
    summary: "How agentic AI expands engineering leverage without removing expert judgment.",
    tag: "Future Teams",
    accent: "from-emerald-300 to-cyan-300",
  },
  {
    slug: "top-five-chiploop-industry-problems",
    title: "Top 5 Industry Problems ChipLoop Addresses",
    summary: "A short priority view of the biggest industry workflow problems ChipLoop is positioned to solve.",
    tag: "Industry",
    accent: "from-cyan-300 to-violet-300",
  },
  {
    slug: "future-end-to-end-ic-engineer",
    title: "The Future End-to-End IC Engineer",
    summary: "How agentic and generative AI can help engineers define, run, fix, and iterate across the full chip journey.",
    tag: "Future Teams",
    accent: "from-amber-300 to-emerald-300",
  },
  {
    slug: "agentic-ai-future-chip-design",
    title: "Agentic AI and the Future of Chip Design",
    summary: "How AI assistance, copilots, agentic workflows, and traditional EDA reference flows can work together.",
    tag: "Agentic AI",
    accent: "from-cyan-300 to-rose-300",
  },
  {
    slug: "ask-this-run-engineering-review",
    title: "Why Ask This Run Changes Engineering Review",
    summary: "How run-grounded questions help engineers inspect logs, artifacts, warnings, and next steps without hunting through files.",
    tag: "Run Review",
    accent: "from-emerald-300 to-violet-300",
  },
  {
    slug: "navigating-loops-engineering-context",
    title: "Navigating Loops and Engineering Context",
    summary: "How ChipLoop helps teams define, configure, and run connected engineering loops, using the PWM reference journey as an example.",
    tag: "Loops",
    accent: "from-violet-300 to-amber-300",
  },
  {
    slug: "prompt-based-chip-design-to-chiploop",
    title: "From Prompt-Based Chip Design to ChipLoop",
    summary: "Why standalone prompts are not enough for real chip work, and how ChipLoop connects intent, tools, artifacts, checks, and handoffs.",
    tag: "ChipLoop",
    accent: "from-rose-300 to-cyan-300",
  },
];

export default function BlogsPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="blogs" showMarketplace showSettings={false} />
      <section className="w-full border-b border-slate-800 px-4 py-10 sm:px-6 sm:py-14">
        <div className="mx-auto max-w-[1440px]">
          <div className="max-w-5xl">
            <div className="font-['Segoe_Print','Bradley_Hand',cursive] text-xl font-bold text-amber-300">ChipLoop Blog</div>
            <h1 className="mt-3 max-w-4xl font-['Segoe_Print','Bradley_Hand',cursive] text-5xl font-extrabold leading-[1.08] text-white sm:text-7xl">
              Ideas for connected silicon development.
            </h1>
            <p className="mt-5 max-w-3xl text-lg leading-8 text-slate-300">
              Practical notes on agentic AI, connected chip workflows, HEM, Smart Context, product journeys, and semiconductor engineering productivity.
            </p>
          </div>

          <div className="mt-10 grid gap-5 md:grid-cols-2 xl:grid-cols-3">
            {articles.map((article) => (
              <button
                key={article.slug}
                type="button"
                onClick={() => router.push(`/blogs/${article.slug}`)}
                className="group overflow-hidden rounded-2xl border border-slate-800 bg-slate-900/70 p-0 text-left shadow-xl shadow-slate-950/25 transition hover:-translate-y-1 hover:border-cyan-300 hover:bg-slate-900"
              >
                <div className={`h-1.5 bg-gradient-to-r ${article.accent}`} />
                <div className="p-5">
                  <div className="flex items-center justify-between gap-3">
                    <span className="rounded-full border border-slate-700 bg-slate-950/70 px-3 py-1 text-xs font-bold uppercase text-cyan-200">
                      {article.tag}
                    </span>
                    <span className="text-sm font-bold text-slate-500 transition group-hover:text-cyan-200">Read</span>
                  </div>
                  <div className="mt-5 font-['Segoe_Print','Bradley_Hand',cursive] text-2xl font-bold leading-snug text-white">{article.title}</div>
                  <p className="mt-4 text-sm leading-6 text-slate-300">{article.summary}</p>
                </div>
              </button>
            ))}
          </div>
        </div>
      </section>
    </main>
  );
}
