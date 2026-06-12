"use client";

import { Suspense, useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import TopNav from "@/components/TopNav";

const supabase = createClientComponentClient();

const automationSnippets = {
  cli: [
    { title: "Install", code: "pip install chiploop-sdk" },
    { title: "Check setup", code: "chiploop doctor" },
    { title: "Run Arch2RTL", code: "chiploop run arch2rtl --spec spec.md" },
    { title: "Download artifacts", code: "chiploop artifacts download <workflow_id> --name rtl/top.v --out ./outputs" },
  ],
  sdk: [
    { title: "Create client", code: "from chiploop_sdk import ChipLoopClient\n\nclient = ChipLoopClient()" },
    { title: "Run workflow", code: "run = client.run_workflow(\n    \"arch2rtl\",\n    spec_text=\"Create a PWM controller.\"\n)" },
    { title: "Check status", code: "status = client.get_workflow_status(run.workflow_id)\nprint(status.status)" },
    { title: "List artifacts", code: "artifacts = client.list_artifacts(run.workflow_id)\nprint(artifacts)" },
  ],
  ide: [
    { title: "VS Code", code: "ChipLoop: Configure\nChipLoop: Run Arch2RTL" },
    { title: "Current file", code: "Open specs/pwm.md\nRun: ChipLoop: Run Workflow from Current File" },
    { title: "Artifacts", code: "ChipLoop: Check Workflow Status\nChipLoop: Download Artifacts" },
    { title: "Cursor", code: "Use the Cursor terminal:\nchiploop run arch2rtl --spec specs/pwm.md" },
  ],
  github: [
    { title: "Action", code: "uses: ./backend/integrations/github-action\nwith:\n  workflow: arch2rtl\n  spec: specs/pwm.md" },
    { title: "Secrets", code: "CHIPLOOP_BASE_URL\nCHIPLOOP_API_KEY" },
    { title: "Outputs", code: "Upload generated RTL, SDC, UPF, and reports\nas GitHub workflow artifacts" },
    { title: "Review", code: "Run ChipLoop on PR specs\nReview artifacts before merging" },
  ],
};

const paths = [
  ["Products", "Create end-to-end product journeys with staged workflows, configuration, run history, dashboards, and downloads.", "/products", "Explore Products"],
  ["Apps", "Run focused prebuilt workflows for RTL, verification, firmware, system simulation, physical design, validation, and product app generation.", "/apps", "Explore Apps"],
  ["Studio", "Build custom agents and workflows, configure execution settings, and run your own chip design flows.", "/workflow", "Open Studio"],
];

const loopNames = ["Digital", "Analog", "Embedded", "System", "Validation", "Physical Design", "Products"];

const whyRows = [
  ["Separate tools for each loop", "One platform for many chip design loops"],
  ["Manual handoff between stages", "Connected workflow handoff across stages"],
  ["Context scattered across files, logs, and chats", "Engineering context preserved across runs"],
  ["Hard to reproduce setup", "Reusable Apps, Products, and Studio workflows"],
  ["Debug requires chasing artifacts manually", "Logs, dashboards, artifacts, and ZIPs in one place"],
  ["Customization requires flow engineering", "Configurable agents, tools, stages, and run settings"],
  ["Product progress tracked manually", "Product-level orchestration and run history"],
];

function LandingPageContent() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);
  const [loginLoading, setLoginLoading] = useState(false);
  const [automationMode, setAutomationMode] = useState<"cli" | "sdk" | "ide" | "github">("cli");
  const [automationStep, setAutomationStep] = useState(0);

  useEffect(() => {
    const getSession = async () => {
      const {
        data: { session },
      } = await supabase.auth.getSession();
      setUserEmail(session?.user?.email || null);
    };
    getSession();
  }, []);

  useEffect(() => {
    setAutomationStep(0);
    const timer = window.setInterval(() => {
      setAutomationStep((current) => (current + 1) % automationSnippets[automationMode].length);
    }, 2600);
    return () => window.clearInterval(timer);
  }, [automationMode]);

  const goTo = async (path: string) => {
    setLoginLoading(true);
    if (userEmail) {
      router.push(path);
      return;
    }
    const {
      data: { session },
    } = await supabase.auth.getSession();
    router.push(session ? path : `/login?next=${encodeURIComponent(path)}`);
  };

  const startGuidedDemo = () => goTo("/apps/arch2rtl?guided=1");

  if (loginLoading) {
    return (
      <main className="flex min-h-screen items-center justify-center bg-slate-950 text-white">
        <div className="text-slate-300">Redirecting...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="home" showMarketplace showSettings={false} className="fixed left-0 top-0 z-50 w-full" />

      <section className="mx-auto flex max-w-7xl flex-col items-center px-4 pb-12 pt-36 text-center sm:px-6 sm:pb-16 sm:pt-32">
        <div className="mb-5 rounded-full border border-cyan-400/30 bg-cyan-400/10 px-4 py-2 text-xs font-semibold text-cyan-200 sm:text-sm">
          Products, Apps, Studio, and connected chip design loops
        </div>
        <h1 className="max-w-6xl text-4xl font-extrabold tracking-tight text-white sm:text-5xl md:text-7xl">
          Agentic AI Platform for Chip Design and Implementation
        </h1>
        <p className="mt-6 max-w-4xl text-base leading-7 text-slate-300 sm:mt-7 sm:text-lg sm:leading-8">
          Define, configure, and run AI-powered workflows from specs to RTL, verification, firmware, system software,
          co-simulation, validation, physical design, and product handoff.
        </p>
        <div className="mt-8 flex w-full flex-col gap-4 sm:mt-10 sm:w-auto sm:flex-row">
          <button onClick={() => goTo("/products")} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 shadow-lg shadow-cyan-950/30 transition hover:bg-cyan-300 sm:w-auto">
            Explore Products
          </button>
          <button onClick={() => goTo("/apps")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
            Explore Apps
          </button>
          <button onClick={() => goTo("/workflow")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
            Open Studio
          </button>
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-4 py-10 text-center sm:px-6 sm:py-14">
        <h2 className="text-3xl font-extrabold sm:text-4xl">One Platform. Many Chip Design Loops. Connected Engineering Context.</h2>
        <p className="mx-auto mt-4 max-w-4xl text-base leading-7 text-slate-300">
          ChipLoop keeps design intent, workflow settings, logs, artifacts, dashboards, and handoff context connected as work moves across
          digital, analog, embedded, system, validation, physical design, and product workflows.
        </p>
        <div className="mt-8 flex flex-col justify-center gap-4 sm:flex-row">
          <button onClick={startGuidedDemo} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 hover:bg-cyan-300 sm:w-auto">
            Start Arch2RTL Demo
          </button>
          <button onClick={() => router.push("/loops")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Loops
          </button>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="grid grid-cols-1 gap-5 md:grid-cols-3">
          {paths.map(([title, body, href, cta]) => (
            <article key={title} className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
              <h3 className="text-xl font-bold text-cyan-300">{title}</h3>
              <p className="mt-3 min-h-24 text-sm leading-6 text-slate-300">{body}</p>
              <button onClick={() => goTo(href)} className="mt-5 rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
                {cta}
              </button>
            </article>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="text-center">
          <h2 className="text-3xl font-extrabold">Define. Configure. Run.</h2>
        </div>
        <div className="mt-8 grid grid-cols-1 gap-5 md:grid-cols-3">
          {[
            ["Define", "Start from specs, starter products, existing workflows, or design intent."],
            ["Configure", "Choose stages, agents, tools, coverage goals, handoff sources, and run settings."],
            ["Run", "Track execution logs, dashboards, artifacts, failures, coverage, and ZIP downloads."],
          ].map(([title, body]) => (
            <div key={title} className="rounded-xl bg-slate-900 p-6 ring-1 ring-slate-800">
              <h3 className="text-lg font-bold text-white">{title}</h3>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="mb-8 text-center">
          <h2 className="text-3xl font-extrabold">Explore Chip Design Loops</h2>
          <p className="mx-auto mt-3 max-w-3xl text-slate-400">
            Each loop connects purpose-built agents, prebuilt workflows, configuration settings, dashboards, and handoff packages.
          </p>
        </div>
        <div className="grid grid-cols-1 gap-4 sm:grid-cols-2 lg:grid-cols-4">
          {loopNames.map((loop) => (
            <button key={loop} onClick={() => router.push("/loops")} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-left hover:border-cyan-400">
              <h3 className="font-bold text-cyan-300">{loop}</h3>
              <p className="mt-2 text-sm leading-6 text-slate-300">Explore agents, Apps, dashboards, and handoff paths.</p>
            </button>
          ))}
        </div>
        <div className="mt-7 text-center">
          <button onClick={() => router.push("/loops")} className="rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300">
            Explore Loops
          </button>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-5 sm:p-8 md:p-10">
          <div className="mb-6">
            <h2 className="text-3xl font-extrabold">Why ChipLoop</h2>
            <p className="mt-3 max-w-4xl text-slate-300">
              Traditional chip execution spreads work across disconnected tools, files, and teams. ChipLoop keeps the execution path connected.
            </p>
          </div>
          <div className="overflow-hidden rounded-xl border border-slate-800">
            <div className="grid grid-cols-2 bg-slate-950 text-sm font-bold text-cyan-200">
              <div className="border-r border-slate-800 p-4">Traditional Execution</div>
              <div className="p-4">ChipLoop Execution</div>
            </div>
            {whyRows.map(([traditional, chiploop]) => (
              <div key={traditional} className="grid grid-cols-2 border-t border-slate-800 text-sm leading-6">
                <div className="border-r border-slate-800 p-4 text-slate-400">{traditional}</div>
                <div className="p-4 text-slate-100">{chiploop}</div>
              </div>
            ))}
          </div>
          <div className="mt-6 flex flex-col gap-3 sm:flex-row">
            <button onClick={() => goTo("/products")} className="rounded-lg bg-cyan-400 px-5 py-3 font-bold text-slate-950 hover:bg-cyan-300">
              Explore Products
            </button>
            <button onClick={() => goTo("/workflow")} className="rounded-lg border border-slate-700 px-5 py-3 font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              Open Studio
            </button>
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-5 sm:p-8 md:p-10">
          <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr] lg:items-center">
            <div>
              <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Developer Automation</p>
              <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">Use ChipLoop from CLI, SDK, IDE, or GitHub</h2>
              <p className="mt-4 leading-7 text-slate-300">
                Start in Products, Apps, or Studio. When your workflow needs scripts, local editor workflows, repo automation,
                or private runners, ChipLoop developer automation keeps the same execution context connected.
              </p>
              <div className="mt-6 flex flex-wrap gap-3">
                {[
                  ["cli", "CLI"],
                  ["sdk", "Python SDK"],
                  ["ide", "VS Code / Cursor"],
                  ["github", "GitHub"],
                ].map(([mode, label]) => (
                  <button
                    key={mode}
                    onClick={() => setAutomationMode(mode as "cli" | "sdk" | "ide" | "github")}
                    className={`rounded-lg px-4 py-2 text-sm font-bold transition ${
                      automationMode === mode
                        ? "bg-cyan-400 text-slate-950"
                        : "border border-slate-700 text-slate-300 hover:border-cyan-300 hover:text-cyan-200"
                    }`}
                  >
                    {label}
                  </button>
                ))}
                <button onClick={() => router.push("/pricing")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-300 transition hover:border-cyan-300 hover:text-cyan-200">
                  View Pricing
                </button>
              </div>
              <p className="mt-4 text-sm text-cyan-100/80">Developer automation is available on Pro, Pro Max, and Enterprise plans.</p>
            </div>
            <div className="overflow-hidden rounded-xl border border-slate-700 bg-slate-950 shadow-2xl">
              <div className="flex items-center justify-between border-b border-slate-800 px-4 py-3">
                <div className="flex gap-2">
                  <span className="h-3 w-3 rounded-full bg-red-400" />
                  <span className="h-3 w-3 rounded-full bg-yellow-400" />
                  <span className="h-3 w-3 rounded-full bg-emerald-400" />
                </div>
                <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">
                  {automationSnippets[automationMode][automationStep].title}
                </div>
              </div>
              <pre className="min-h-36 overflow-x-auto whitespace-pre-wrap break-words px-4 py-4 text-left text-xs leading-6 text-cyan-100 sm:min-h-44 sm:px-5 sm:py-5 sm:text-sm sm:leading-7">
                <code>{automationSnippets[automationMode][automationStep].code}</code>
              </pre>
              <div className="flex gap-2 border-t border-slate-800 px-4 py-3">
                {automationSnippets[automationMode].map((item, index) => (
                  <button
                    key={item.title}
                    onClick={() => setAutomationStep(index)}
                    aria-label={`Show ${item.title}`}
                    className={`h-2 flex-1 rounded-full transition ${index === automationStep ? "bg-cyan-400" : "bg-slate-800"}`}
                  />
                ))}
              </div>
            </div>
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-5xl px-4 py-12 text-center sm:px-6 sm:py-16">
        <h2 className="text-2xl font-extrabold sm:text-3xl">Start Building Connected Chip Workflows</h2>
        <p className="mt-4 text-slate-300">
          Begin with the guided Arch2RTL demo, explore chip design loops, or launch prebuilt Apps and Product journeys.
        </p>
        <div className="mt-8 flex flex-col justify-center gap-4 sm:flex-row">
          <button onClick={startGuidedDemo} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 hover:bg-cyan-300 sm:w-auto">
            Start Arch2RTL Demo
          </button>
          <button onClick={() => router.push("/loops")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Loops
          </button>
          <button onClick={() => goTo("/apps")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Apps
          </button>
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-cyan-400/30 bg-cyan-400/10 p-6 text-center">
          <h2 className="text-2xl font-extrabold text-white">Events</h2>
          <p className="mx-auto mt-3 max-w-3xl text-slate-300">
            Join ChipLoop workshops and webinars to learn agentic chip design workflows, product journeys, and implementation best practices.
          </p>
          <button onClick={() => router.push("/events")} className="mt-6 rounded-lg bg-cyan-400 px-5 py-3 font-bold text-slate-950 hover:bg-cyan-300">
            View Events
          </button>
        </div>
      </section>

      <footer className="border-t border-slate-800 bg-slate-950 px-6 py-8 text-center text-sm text-slate-500">
        <p>Copyright 2026 ChipLoop</p>
      </footer>
    </main>
  );
}

export default function LandingPage() {
  return (
    <Suspense fallback={<div className="p-10 text-center">Loading...</div>}>
      <LandingPageContent />
    </Suspense>
  );
}
