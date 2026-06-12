"use client";

import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

const rows = [
  ["Separate tools for each loop", "One platform for many chip design loops"],
  ["Manual handoff between stages", "Connected workflow handoff across stages"],
  ["Context scattered across files, logs, and chats", "Engineering context preserved across runs"],
  ["Hard to reproduce setup", "Reusable Apps, Products, and Studio workflows"],
  ["Debug requires chasing artifacts manually", "Logs, dashboards, artifacts, and ZIPs in one place"],
  ["Customization requires flow engineering", "Configurable agents, tools, stages, and run settings"],
  ["Product progress tracked manually", "Product-level orchestration and run history"],
];

const actions = [
  ["Explore Loops", "/loops"],
  ["Explore Products", "/products"],
  ["Explore Apps", "/apps"],
  ["Explore Studio", "/workflow"],
];

export default function WhyChipLoopPage() {
  const router = useRouter();

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav showMarketplace showSettings={false} />
      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="max-w-4xl">
          <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Why ChipLoop</div>
          <h1 className="mt-3 text-4xl font-extrabold tracking-tight sm:text-5xl">
            One Platform for Connected Chip Execution
          </h1>
          <p className="mt-4 text-lg leading-8 text-slate-300">
            Traditional chip development spreads execution across separate tools, custom scripts, emails, folders,
            and review meetings. ChipLoop keeps the loops connected so design intent, run configuration, logs,
            artifacts, dashboards, and handoff context move together.
          </p>
        </div>

        <div className="mt-8 overflow-hidden rounded-xl border border-slate-800 bg-slate-900/80">
          <div className="grid grid-cols-1 bg-slate-950 text-sm font-bold text-cyan-200 sm:grid-cols-2">
            <div className="border-b border-slate-800 p-4 sm:border-b-0 sm:border-r">Traditional Execution</div>
            <div className="p-4">ChipLoop Execution</div>
          </div>
          {rows.map(([traditional, chiploop]) => (
            <div key={traditional} className="grid grid-cols-1 border-t border-slate-800 text-sm leading-6 sm:grid-cols-2">
              <div className="border-b border-slate-800 p-4 text-slate-400 sm:border-b-0 sm:border-r">{traditional}</div>
              <div className="p-4 text-slate-100">{chiploop}</div>
            </div>
          ))}
        </div>

        <section className="mt-10 rounded-xl border border-cyan-400/30 bg-cyan-400/10 p-6 sm:p-8">
          <h2 className="text-2xl font-extrabold">Define. Configure. Run. Review. Improve.</h2>
          <p className="mt-3 max-w-4xl leading-7 text-slate-300">
            Start from a product, a prebuilt app, or a custom Studio workflow. Configure the settings each loop needs,
            run the agents, then review dashboards and downloadable handoff packages from the same product context.
          </p>
          <div className="mt-6 flex flex-col gap-3 sm:flex-row sm:flex-wrap">
            {actions.map(([label, href], index) => (
              <button
                key={label}
                onClick={() => router.push(href)}
                className={`rounded-lg px-5 py-3 text-sm font-bold transition ${
                  index === 0
                    ? "bg-cyan-400 text-slate-950 hover:bg-cyan-300"
                    : "border border-slate-700 text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
                }`}
              >
                {label}
              </button>
            ))}
          </div>
        </section>
      </section>
    </main>
  );
}
