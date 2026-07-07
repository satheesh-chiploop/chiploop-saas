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
  ["Loops", "Choose your chip design domain.", "/loops", "Explore Loops"],
  ["Products", "Build complete chip journeys.", "/products", "Explore Products"],
  ["Apps", "Run ready-made chip workflows.", "/apps", "Explore Apps"],
  ["Studio", "Create custom agents and workflows.", "/workflow", "Open Studio"],
  ["Marketplace", "Reuse approved engineering flows.", "/marketplace", "Explore Marketplace"],
];

const platformStats = [
  ["195+", "Agents"],
  ["40+", "Apps"],
  ["11+", "Workflow Templates"],
  ["8+", "Reference Journeys"],
  ["5+", "Product Journeys"],
  ["SDK + CLI + Studio", "Developer Access"],
];

const subscriptionLoops = [
  {
    name: "Digital Design",
    body: "Requirements, design intent, spec-to-RTL, RTL generation, review, and handoff.",
  },
  {
    name: "Digital Implementation",
    body: "Synthesis, implementation setup, constraints, reports, closure, and tapeout handoff.",
  },
  {
    name: "Mixed Signal",
    body: "System RTL, analog/digital partitioning, models, smoke tests, and system synthesis.",
  },
  {
    name: "Firmware/Software",
    body: "Firmware, drivers, software examples, validation, co-simulation, and demos.",
  },
  {
    name: "Validation",
    body: "Validation plans, bring-up checklists, logs, dashboards, debug, and readiness packages.",
  },
];

const accessModel = [
  ["Plan", "Platform limits"],
  ["Loop", "Engineering domain"],
  ["Core / Advanced", "Automation depth"],
  ["Credits", "Usage volume"],
];

const agentSegments = [
  { key: "system", label: "System", color: "#a78bfa" },
  { key: "analog", label: "Analog", color: "#fb7185" },
  { key: "digital", label: "Digital", color: "#22d3ee" },
  { key: "firmware", label: "Firmware", color: "#34d399" },
  { key: "software", label: "Software + validation + co-sim", color: "#fbbf24" },
  { key: "product", label: "Product demo", color: "#f472b6" },
];

const workflowAgentChart = [
  {
    label: "Digital IP Product",
    example: "PWM to demo",
    agents: { system: 6, analog: 0, digital: 36, firmware: 10, software: 12, product: 6 },
  },
  {
    label: "Mixed-Signal IP Product",
    example: "Temp Monitor SoC",
    agents: { system: 12, analog: 18, digital: 35, firmware: 10, software: 12, product: 8 },
  },
  {
    label: "Digital IP + Tapeout",
    example: "RTL to GDS/signoff",
    agents: { system: 5, analog: 0, digital: 73, firmware: 0, software: 0, product: 7 },
  },
  {
    label: "Mixed-Signal Product + Tapeout",
    example: "SoC to demo + GDS",
    agents: { system: 16, analog: 22, digital: 48, firmware: 12, software: 14, product: 8 },
  },
];

const workflowAgentMax = 120;
const workflowAgentPlotHeight = 288;

const marketplaceFlow = [
  ["Agents", "Specialized AI and tool agents for chip tasks"],
  ["Workflows", "Reusable execution flows with saved context"],
  ["Apps", "Packaged workflows users can run or customize"],
  ["Products", "Connected journeys from requirement to handoff"],
  ["Marketplace", "Approved apps and products teams can reuse"],
];

const endToEndJourney = [
  "Requirements",
  "RTL",
  "Verification",
  "Firmware",
  "Software",
  "Co-simulation",
  "Tapeout",
  "Validation",
  "Product Demo",
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
        <h1 className="max-w-6xl text-4xl font-extrabold tracking-tight text-white sm:text-5xl md:text-7xl">
          All-in-one agentic AI platform for chip design
        </h1>
        <p className="mt-6 max-w-4xl text-base leading-7 text-slate-300 sm:mt-7 sm:text-lg sm:leading-8">
          Help one engineer or a small team move from requirements to RTL, verification, firmware, software, co-simulation, tapeout, validation, and product demo in one connected platform.
        </p>
        <div className="mt-8 flex w-full flex-col gap-4 sm:mt-10 sm:w-auto sm:flex-row">
          <button onClick={() => router.push("/book-demo")} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 shadow-lg shadow-cyan-950/30 transition hover:bg-cyan-300 sm:w-auto">
            Book Demo
          </button>
          <button onClick={() => router.push("/loops")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
            Explore Loops
          </button>
          <button onClick={() => goTo("/products")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
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

      <section className="mx-auto max-w-7xl px-4 py-8 sm:px-6">
        <div className="grid grid-cols-2 gap-3 sm:grid-cols-3 lg:grid-cols-6">
          {platformStats.map(([value, label]) => (
            <div key={label} className="rounded-xl border border-slate-800 bg-slate-900/70 px-4 py-5 text-center">
              <div className="break-words text-xl font-extrabold leading-tight text-cyan-300 sm:text-2xl">{value}</div>
              <div className="mt-2 text-xs font-semibold uppercase tracking-wide text-slate-400">{label}</div>
            </div>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="mx-auto max-w-4xl text-center">
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Choose Your Chip Design Loop</p>
            <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">
              One platform. Five chip design loops. Connected engineering context.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              Start with one Core loop. Add Advanced capability or more credits as your work grows.
            </p>
          </div>
          <div className="mt-8 grid grid-cols-1 gap-4 md:grid-cols-2 xl:grid-cols-5">
            {subscriptionLoops.map((loop) => (
              <article key={loop.name} className="rounded-xl border border-slate-800 bg-slate-950/70 p-5">
                <h3 className="text-lg font-extrabold text-cyan-200">{loop.name}</h3>
                <p className="mt-3 min-h-28 text-sm leading-6 text-slate-400">{loop.body}</p>
              </article>
            ))}
          </div>
          <div className="mt-6 grid grid-cols-1 gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {accessModel.map(([title, body]) => (
              <div key={title} className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-center">
                <div className="font-extrabold text-slate-100">{title}</div>
                <div className="mt-1 text-sm text-slate-400">{body}</div>
              </div>
            ))}
          </div>
          <div className="mt-7 text-center">
            <button onClick={() => router.push("/loops")} className="rounded-lg border border-cyan-700 px-5 py-3 text-sm font-bold text-cyan-100 hover:border-cyan-300 hover:text-cyan-200">
              Explore Design Loops
            </button>
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-8 sm:px-6 sm:py-10">
        <div className="text-center">
          <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Explore ChipLoop</p>
          <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">Start where you need.</h2>
        </div>
        <div className="mt-8 grid grid-cols-1 gap-5 md:grid-cols-2 xl:grid-cols-5">
          {paths.map(([title, body, href, cta]) => (
            <article key={title} className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 text-center">
              <h3 className="text-2xl font-extrabold text-cyan-300">{title}</h3>
              <p className="mt-3 min-h-12 text-base font-semibold leading-6 text-slate-200">{body}</p>
              <button onClick={() => goTo(href)} className="mt-5 rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
                {cta}
              </button>
            </article>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="mx-auto max-w-4xl text-center">
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Connected Chip Journey</p>
            <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">
              From requirement capture to product demo without losing engineering context.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              ChipLoop keeps each stage connected, so outputs, logs, dashboards, and decisions carry forward instead of living in disconnected tools.
            </p>
          </div>
          <div className="mt-8 flex flex-col gap-3 xl:flex-row xl:items-stretch">
            {endToEndJourney.map((stage, index) => (
              <div key={stage} className="contents xl:flex xl:items-center">
                <div className="rounded-xl border border-slate-800 bg-slate-950/70 px-4 py-4 text-center text-sm font-bold text-slate-100 xl:flex-1">
                  {stage}
                </div>
                {index < endToEndJourney.length - 1 && (
                  <div className="flex items-center justify-center text-lg font-bold text-slate-600" aria-hidden="true">
                    <span className="xl:hidden">↓</span>
                    <span className="hidden xl:inline">→</span>
                  </div>
                )}
              </div>
            ))}
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="grid gap-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8 lg:grid-cols-[0.8fr_1.2fr] lg:items-center">
          <div>
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Workflow Scale</p>
            <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">
              Agent coverage grows with journey complexity.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              As a chip journey grows from a digital IP block to mixed-signal products, tapeout, validation, and demos, ChipLoop keeps the agents, tools, artifacts, dashboards, and handoffs connected.
            </p>
            <div className="mt-5 grid grid-cols-1 gap-3 text-sm text-slate-300 sm:grid-cols-2">
              {agentSegments.map((segment) => (
                <div key={segment.key} className="flex items-center gap-2">
                  <span className="h-3 w-3 rounded-sm" style={{ backgroundColor: segment.color }} />
                  <span>{segment.label}</span>
                </div>
              ))}
            </div>
          </div>
          <div className="min-w-0">
            <div className="grid grid-cols-[24px_40px_1fr] gap-4">
              <div className="flex h-72 items-center justify-center">
                <span className="-rotate-90 whitespace-nowrap text-xs font-semibold uppercase tracking-wide text-slate-500">
                  Number of agents orchestrated
                </span>
              </div>
              <div className="relative h-72 border-r border-slate-800 text-right text-xs text-slate-500">
                <span className="absolute right-3 top-0 -translate-y-1/2">120</span>
                <span className="absolute right-3 top-1/3 -translate-y-1/2">80</span>
                <span className="absolute right-3 top-2/3 -translate-y-1/2">40</span>
                <span className="absolute bottom-0 right-3 translate-y-1/2">0</span>
              </div>
              <div>
                <div className="relative h-72 border-b border-slate-700 px-1">
                  <div className="pointer-events-none absolute inset-x-1 bottom-0 top-0 flex flex-col justify-between">
                    <span className="border-t border-slate-800" />
                    <span className="border-t border-slate-800" />
                    <span className="border-t border-slate-800" />
                    <span className="border-t border-slate-700" />
                  </div>
                  <div className="relative grid h-full grid-cols-4 items-end gap-3 sm:gap-5">
                    {workflowAgentChart.map((item) => {
                      const totalAgents = agentSegments.reduce((sum, segment) => sum + item.agents[segment.key as keyof typeof item.agents], 0);
                      const barHeight = Math.max((totalAgents / workflowAgentMax) * workflowAgentPlotHeight, 8);
                      return (
                        <div key={item.label} className="relative flex h-full min-w-0 items-end justify-center">
                          <div
                            className="absolute text-sm font-bold text-cyan-200"
                            style={{ bottom: `${barHeight + 10}px` }}
                          >
                            {totalAgents}
                          </div>
                          <div
                            className="flex w-full max-w-20 flex-col-reverse overflow-hidden rounded-t-md shadow-lg shadow-slate-950/30"
                            style={{ height: `${barHeight}px` }}
                          >
                            {agentSegments.map((segment) => {
                              const segmentAgents = item.agents[segment.key as keyof typeof item.agents];
                              if (!segmentAgents) return null;
                              return (
                                <div
                                  key={segment.key}
                                  title={`${segment.label}: ${segmentAgents} agents`}
                                  className="w-full border-t border-slate-950/40"
                                  style={{
                                    height: `${(segmentAgents / totalAgents) * 100}%`,
                                    backgroundColor: segment.color,
                                  }}
                                />
                              );
                            })}
                          </div>
                        </div>
                      );
                    })}
                  </div>
                </div>
                <div className="mt-3 grid grid-cols-4 gap-3 px-1 text-center sm:gap-5">
                  {workflowAgentChart.map((item) => (
                    <div key={item.label} className="min-h-20">
                      <div className="text-xs font-bold leading-4 text-slate-100">{item.label}</div>
                      <div className="mt-1 text-xs leading-4 text-slate-500">Ex: {item.example}</div>
                    </div>
                  ))}
                </div>
                <div className="mt-3 text-center text-xs font-semibold uppercase tracking-wide text-slate-500">Workflows</div>
              </div>
            </div>
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Reusable Workflow Marketplace</p>
            <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">
              Package engineering know-how into reusable chip design products.
            </h2>
            <p className="mt-4 leading-7 text-slate-300">
              ChipLoop turns individual agents and workflows into private apps, product journeys, and marketplace-ready solutions that other teams can run without rebuilding the environment.
            </p>
          </div>
          <div className="mt-8 grid grid-cols-1 gap-3 md:grid-cols-[1fr_auto_1fr_auto_1fr_auto_1fr_auto_1fr] md:items-stretch">
            {marketplaceFlow.map(([title, body], index) => (
              <div key={title} className="contents">
                <article className="rounded-xl border border-slate-800 bg-slate-950/70 p-4 text-center">
                  <div className="text-lg font-extrabold text-cyan-200">{title}</div>
                  <p className="mt-2 text-sm leading-6 text-slate-400">{body}</p>
                </article>
                {index < marketplaceFlow.length - 1 && (
                  <div className="flex items-center justify-center text-xl font-bold text-slate-600" aria-hidden="true">
                    <span className="md:hidden">↓</span>
                    <span className="hidden md:inline">→</span>
                  </div>
                )}
              </div>
            ))}
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="text-center">
          <h2 className="text-3xl font-extrabold">Design Intent to Execution</h2>
          <p className="mx-auto mt-3 max-w-3xl text-base leading-7 text-slate-300">
            ChipLoop turns complex multi-dimensional chip design workflows into connected, traceable execution loops.
          </p>
        </div>
        <div className="mt-8 grid grid-cols-1 items-stretch gap-4 md:grid-cols-[1fr_auto_1fr_auto_1fr]">
          {[
            ["01", "Define", "Specs, products, or workflows"],
            ["02", "Configure", "Stages, tools, agents, goals"],
            ["03", "Run", "Logs, dashboards, artifacts"],
          ].map(([step, title, body], index) => (
            <div key={title} className="contents">
              <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-6 text-center">
                <div className="mx-auto flex h-10 w-10 items-center justify-center rounded-full bg-cyan-400 text-sm font-extrabold text-slate-950">
                  {step}
                </div>
                <h3 className="mt-4 text-xl font-extrabold text-white">{title}</h3>
                <p className="mt-2 text-sm leading-6 text-slate-300">{body}</p>
              </div>
              {index < 2 ? (
                <div className="flex items-center justify-center text-3xl font-extrabold text-cyan-300 md:px-2">
                  <span className="hidden md:inline">→</span>
                  <span className="md:hidden">↓</span>
                </div>
              ) : null}
            </div>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-4 py-10 sm:px-6 sm:py-14">
        <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-5 sm:p-8 md:p-10">
          <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr] lg:items-center">
            <div>
              <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Developer Automation</p>
              <h2 className="mt-3 text-2xl font-extrabold text-white sm:text-3xl">Automate from CLI, SDK, IDE, or GitHub</h2>
              <p className="mt-4 leading-7 text-slate-300">
                Use the same ChipLoop context in scripts, editors, CI, and private runners.
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
              </div>
              <p className="mt-4 text-sm text-cyan-100/80">Available for scripted, local, and CI-driven workflows.</p>
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
          Begin with the guided Arch2RTL demo, then continue through Products, Apps, or Studio.
        </p>
        <div className="mt-8 flex flex-col justify-center gap-4 sm:flex-row">
          <button onClick={() => router.push("/book-demo")} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 hover:bg-cyan-300 sm:w-auto">
            Book Demo
          </button>
          <button onClick={startGuidedDemo} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
            Start Arch2RTL Demo
          </button>
          <button onClick={() => goTo("/products")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Products
          </button>
          <button onClick={() => goTo("/apps")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Apps
          </button>
          <button onClick={() => goTo("/workflow")} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300 sm:w-auto">
            Explore Studio
          </button>
        </div>
      </section>

      <footer className="border-t border-slate-800 bg-slate-950 px-6 py-8 text-center text-sm text-slate-500">
        <div className="mb-4 flex flex-wrap justify-center gap-4 text-slate-400">
          <button onClick={() => router.push("/events")} className="hover:text-cyan-200">Events</button>
          <button onClick={() => router.push("/help")} className="hover:text-cyan-200">Playbook</button>
          <button onClick={() => router.push("/why-chiploop")} className="hover:text-cyan-200">Why ChipLoop</button>
          <button onClick={() => router.push("/webinar/register")} className="hover:text-cyan-200">Webinar</button>
        </div>
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
