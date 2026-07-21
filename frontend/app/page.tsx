"use client";

import { Suspense, useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { FaBrain, FaCog, FaCompressAlt, FaFileAlt, FaInfinity, FaMicrochip, FaPlay, FaStore, FaTh, FaUserEdit } from "react-icons/fa";
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
  {
    title: "Loops",
    body: "Choose your chip design domain.",
    href: "/loops",
    cta: "Explore Loops",
    icon: FaInfinity,
    iconAccent: "text-amber-300",
    border: "border-cyan-400/55",
    hover: "hover:border-cyan-300 hover:shadow-cyan-950/35",
  },
  {
    title: "Products",
    body: "Build complete chip journeys.",
    href: "/products",
    cta: "Explore Products",
    icon: FaMicrochip,
    iconAccent: "text-amber-300",
    border: "border-pink-400/55",
    hover: "hover:border-pink-300 hover:shadow-pink-950/35",
  },
  {
    title: "Apps",
    body: "Run ready-made chip workflows.",
    href: "/apps",
    cta: "Explore Apps",
    icon: FaTh,
    iconAccent: "text-amber-300",
    border: "border-emerald-400/55",
    hover: "hover:border-emerald-300 hover:shadow-emerald-950/35",
  },
  {
    title: "Studio",
    body: "Create custom agents and workflows.",
    href: "/workflow",
    cta: "Open Studio",
    icon: FaUserEdit,
    iconAccent: "text-amber-300",
    border: "border-violet-400/55",
    hover: "hover:border-violet-300 hover:shadow-violet-950/35",
  },
  {
    title: "Marketplace",
    body: "Reuse approved engineering flows.",
    href: "/marketplace",
    cta: "Explore Marketplace",
    icon: FaStore,
    iconAccent: "text-amber-300",
    border: "border-amber-300/55",
    hover: "hover:border-amber-300 hover:shadow-amber-950/35",
  },
];

const platformStats = [
  ["198+", "Agents", "text-cyan-300"],
  ["43+", "Apps", "text-emerald-300"],
  ["14+", "Workflow Templates", "text-violet-300"],
  ["8+", "Reference Journeys", "text-amber-300"],
  ["5+", "Product Journeys", "text-pink-300"],
  ["SDK + CLI + Studio", "Developer Access", "text-slate-100"],
];

const subscriptionLoops = [
  {
    name: "Digital Design",
    body: "Design intent, architecture-to-RTL, RTL quality, verification setup, and handoff.",
    border: "border-cyan-400/55",
    hover: "hover:border-cyan-300 hover:shadow-cyan-950/35",
  },
  {
    name: "Digital Implementation",
    body: "Synthesis, constraints, timing/power/area reports, DFT/MBIST, RTL-to-GDS, signoff, and tapeout handoff.",
    border: "border-violet-400/55",
    hover: "hover:border-violet-300 hover:shadow-violet-950/35",
  },
  {
    name: "Mixed Signal",
    body: "System and mixed-signal integration across digital RTL, analog models, SoC intent, simulation, and synthesis.",
    border: "border-rose-400/55",
    hover: "hover:border-rose-300 hover:shadow-rose-950/35",
  },
  {
    name: "Firmware/Software",
    body: "Register extraction, HAL, drivers, boot/diagnostics, firmware builds, software services, co-simulation, and demos.",
    border: "border-emerald-400/55",
    hover: "hover:border-emerald-300 hover:shadow-emerald-950/35",
  },
  {
    name: "Validation",
    body: "Validation plans, bench/instrument setup, connectivity, preflight, execution analytics, and reports.",
    border: "border-amber-300/55",
    hover: "hover:border-amber-300 hover:shadow-amber-950/35",
  },
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
    agents: { system: 6, analog: 0, digital: 39, firmware: 10, software: 12, product: 6 },
  },
  {
    label: "Mixed-Signal IP Product",
    example: "Temp Monitor SoC",
    agents: { system: 12, analog: 18, digital: 38, firmware: 10, software: 12, product: 8 },
  },
  {
    label: "Digital IP + Tapeout",
    example: "RTL to GDS/signoff",
    agents: { system: 5, analog: 0, digital: 76, firmware: 0, software: 0, product: 7 },
  },
  {
    label: "Mixed-Signal Product + Tapeout",
    example: "SoC to demo + GDS",
    agents: { system: 16, analog: 22, digital: 51, firmware: 12, software: 14, product: 8 },
  },
];

const workflowAgentMax = 130;
const workflowAgentPlotHeight = 288;
const workflowAgentTicks = [130, 100, 50, 0];

const marketplaceFlow = [
  ["Agents", "Specialized AI and tool agents for chip tasks"],
  ["Workflows", "Reusable execution flows with saved context"],
  ["Apps", "Packaged workflows users can run or customize"],
  ["Products", "Connected journeys from requirement to handoff"],
  ["Marketplace", "Approved apps and products teams can reuse"],
];

const executionSteps = [
  { step: "01", title: "Define", body: "Specs, products, or workflows", icon: FaFileAlt },
  { step: "02", title: "Configure", body: "Stages, tools, agents, goals", icon: FaCog },
  { step: "03", title: "Run", body: "Logs, dashboards, artifacts", icon: FaPlay },
];

const selfRegulatedFeatures = [
  {
    title: "HEM Automatic Runs",
    body: "When a stage passes, ChipLoop can continue to the next selected stage and keep each dashboard linked.",
    icon: FaBrain,
  },
  {
    title: "Smart Context",
    body: "Ask This Run and Ask This Project prioritize relevant logs, reports, and files before calling the model.",
    icon: FaCompressAlt,
  },
  {
    title: "Evidence Stays Connected",
    body: "Workflow IDs, artifacts, logs, answers, and handoffs stay traceable across the silicon journey.",
    icon: FaFileAlt,
  },
];

const endToEndJourney = [
  "Design Intent",
  "RTL",
  "Verification",
  "Firmware",
  "Software",
  "Co-simulation",
  "Tapeout",
  "Validation",
  "Product Demo",
];

const eyebrowClass = "text-xs font-semibold uppercase text-cyan-300";
const sectionTitleClass = "mt-3 max-w-4xl text-2xl font-extrabold leading-tight text-white sm:text-3xl lg:text-4xl";
const sectionBodyClass = "mt-4 max-w-3xl text-base leading-7 text-slate-300";
const cardTitleClass = "text-lg font-bold leading-snug text-white";
const cardBodyClass = "mt-3 text-sm leading-6 text-slate-400";
const landingShellClass = "mx-auto w-full max-w-[1680px]";

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
    <main className="min-h-screen overflow-x-hidden bg-slate-950 text-white">
      <TopNav current="home" showMarketplace showSettings={false} className="fixed left-0 top-0 z-50 w-full" />

      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.16),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_62%,#020617_100%)]">
        <div className={`${landingShellClass} flex flex-col items-center px-4 pb-8 pt-24 text-center sm:px-6 sm:pb-10 sm:pt-28 lg:pt-28`}>
          <h1 className="max-w-[1440px] text-4xl font-extrabold leading-[1.06] text-white min-[420px]:text-5xl sm:text-6xl lg:text-7xl">
            All-in-one agentic AI platform for Silicon Development
          </h1>
          <p className="mt-5 max-w-4xl text-base leading-7 text-slate-300 sm:mt-6 sm:text-xl sm:leading-9">
            Help one engineer or a small team move from requirements to RTL, verification, firmware, software, co-simulation, tapeout, validation, and product demo in one connected platform.
          </p>
          <div className="mt-7 flex w-full flex-col justify-center gap-3 sm:w-auto sm:flex-row sm:flex-wrap">
            <button onClick={() => router.push("/book-demo")} className="w-full rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 shadow-lg shadow-cyan-950/30 transition hover:bg-cyan-300 sm:w-auto">
              Book Demo
            </button>
            <button onClick={startGuidedDemo} className="w-full rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200 sm:w-auto">
              Start Arch2RTL Demo
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
        </div>
      </section>

      <section className="w-full border-b border-slate-800 bg-slate-900/45">
        <div className={`${landingShellClass} px-4 py-8 sm:px-6`}>
          <div className="grid grid-cols-2 gap-3 sm:grid-cols-3 lg:grid-cols-6">
            {platformStats.map(([value, label, color]) => (
              <div key={label} className="rounded-xl border border-slate-800 bg-slate-950/70 px-4 py-5 text-center">
                <div className={`break-words text-2xl font-extrabold leading-tight ${color} sm:text-3xl`}>{value}</div>
                <div className="mt-2 text-xs font-medium uppercase text-slate-400">{label}</div>
              </div>
            ))}
          </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="mx-auto max-w-4xl text-center">
            <p className={eyebrowClass}>Choose Your Chip Design Loop</p>
            <h2 className={`${sectionTitleClass} mx-auto`}>
              One platform. Five chip design loops. Connected engineering context.
            </h2>
            <p className={`${sectionBodyClass} mx-auto`}>
              Start with one Core loop. Add Advanced capability or more credits as your work grows.
            </p>
          </div>
          <div className="mt-8 grid grid-cols-1 gap-4 md:grid-cols-2 xl:grid-cols-5">
            {subscriptionLoops.map((loop) => (
              <article key={loop.name} className={`rounded-xl border-2 ${loop.border} bg-slate-950/70 p-5 shadow-lg shadow-slate-950/20 transition hover:-translate-y-0.5 hover:bg-slate-950 hover:shadow-xl ${loop.hover}`}>
                <h3 className={cardTitleClass}>{loop.name}</h3>
                <p className={`${cardBodyClass} min-h-28`}>{loop.body}</p>
              </article>
            ))}
          </div>
          <div className="mt-7 text-center">
            <button onClick={() => router.push("/loops")} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-100 hover:border-cyan-300 hover:text-cyan-200">
              Explore Design Loops
            </button>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-8 sm:px-6 sm:py-10">
        <div className={landingShellClass}>
        <div className="text-center">
          <p className={eyebrowClass}>Explore ChipLoop</p>
          <h2 className={`${sectionTitleClass} mx-auto`}>Start where you need.</h2>
        </div>
        <div className="mt-8 grid grid-cols-1 gap-5 md:grid-cols-2 xl:grid-cols-5">
          {paths.map(({ title, body, href, cta, icon: Icon, iconAccent, border, hover }) => (
            <article key={title} className={`rounded-xl border-2 ${border} bg-slate-900/70 p-5 text-center shadow-lg shadow-slate-950/20 transition hover:-translate-y-0.5 hover:bg-slate-900 hover:shadow-xl ${hover}`}>
              <div className={`mx-auto flex h-12 w-12 items-center justify-center ${iconAccent}`}>
                <Icon className="h-9 w-9" aria-hidden="true" />
              </div>
              <h3 className="mt-4 text-xl font-bold leading-tight text-white">{title}</h3>
              <p className="mt-3 min-h-12 text-sm leading-6 text-slate-300">{body}</p>
              <button onClick={() => goTo(href)} className="mt-5 rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
                {cta}
              </button>
            </article>
          ))}
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="mx-auto max-w-4xl text-center">
            <p className={eyebrowClass}>Connected Chip Journey</p>
            <h2 className={`${sectionTitleClass} mx-auto`}>
              From requirement capture to product demo without losing engineering context.
            </h2>
            <p className={`${sectionBodyClass} mx-auto`}>
              ChipLoop keeps each stage connected, so outputs, logs, dashboards, and decisions carry forward instead of living in disconnected tools.
            </p>
          </div>
          <div className="mx-auto mt-8 w-full max-w-[1680px] overflow-x-auto pb-2">
            <div className="grid min-w-[980px] grid-cols-[repeat(17,minmax(0,auto))] items-center justify-center gap-1.5 lg:gap-2">
            {endToEndJourney.map((stage, index) => (
              <div key={stage} className="contents">
                <div className="flex h-12 w-[88px] items-center justify-center rounded-lg border border-slate-700 bg-slate-950/70 px-2 text-center text-[10px] font-semibold leading-4 text-slate-100 sm:w-24 md:w-28 md:text-xs lg:w-32">
                  {stage}
                </div>
                {index < endToEndJourney.length - 1 && (
                  <div className="flex h-5 w-5 items-center justify-center rounded-full border border-slate-700 bg-slate-950 text-[10px] font-bold text-slate-500 md:h-6 md:w-6 md:text-xs" aria-hidden="true">
                    {"\u2192"}
                  </div>
                )}
              </div>
            ))}
            </div>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
          <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
            <div className="mx-auto max-w-4xl text-center">
              <p className={eyebrowClass}>Self-regulated Silicon Workflows</p>
              <h2 className={`${sectionTitleClass} mx-auto`}>
                ChipLoop can continue the journey and keep AI context focused.
              </h2>
              <p className={`${sectionBodyClass} mx-auto`}>
                HEM Automatic Runs moves from one passed stage to the next selected stage. Smart Context reduces unnecessary tokens by selecting the evidence that matters before the model answers.
              </p>
            </div>
            <div className="mt-8 grid grid-cols-1 gap-4 md:grid-cols-3">
              {selfRegulatedFeatures.map(({ title, body, icon: Icon }) => (
                <article key={title} className="rounded-xl border-2 border-cyan-400/45 bg-slate-950/70 p-5 text-center shadow-lg shadow-slate-950/20 transition hover:-translate-y-0.5 hover:border-cyan-300 hover:bg-slate-900">
                  <Icon className="mx-auto h-9 w-9 text-amber-300" aria-hidden="true" />
                  <h3 className="mt-4 text-xl font-bold text-white">{title}</h3>
                  <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
                </article>
              ))}
            </div>
          </div>
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
        <div className="grid gap-8 rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8 lg:grid-cols-[0.8fr_1.2fr] lg:items-center">
          <div>
            <p className={eyebrowClass}>Workflow Scale</p>
            <h2 className={sectionTitleClass}>
              Agent coverage grows with journey complexity.
            </h2>
            <p className={sectionBodyClass}>
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
          <div className="min-w-0 overflow-x-auto pb-2">
            <div className="grid min-w-[760px] grid-cols-[24px_40px_1fr] gap-4">
              <div className="flex h-72 items-center justify-center">
                <span className="-rotate-90 whitespace-nowrap text-xs font-medium uppercase text-slate-500">
                  Number of agents orchestrated
                </span>
              </div>
              <div className="relative h-72 border-r border-slate-800 text-right text-xs text-slate-500">
                {workflowAgentTicks.map((tick) => (
                  <span
                    key={tick}
                    className="absolute right-3 translate-y-1/2"
                    style={{ bottom: `${(tick / workflowAgentMax) * 100}%` }}
                  >
                    {tick}
                  </span>
                ))}
              </div>
              <div>
                <div className="relative h-72 border-b border-slate-700 px-1">
                  {workflowAgentTicks.map((tick) => (
                    <span
                      key={tick}
                      className={`pointer-events-none absolute inset-x-1 border-t ${tick === 0 ? "border-slate-700" : "border-slate-800"}`}
                      style={{ bottom: `${(tick / workflowAgentMax) * 100}%` }}
                    />
                  ))}
                  <div className="relative grid h-full grid-cols-4 items-end gap-3 sm:gap-5">
                    {workflowAgentChart.map((item) => {
                      const totalAgents = agentSegments.reduce((sum, segment) => sum + item.agents[segment.key as keyof typeof item.agents], 0);
                      const barHeight = Math.max((totalAgents / workflowAgentMax) * workflowAgentPlotHeight, 8);
                      return (
                        <div key={item.label} className="relative flex h-full min-w-0 items-end justify-center">
                          <div
                            className="absolute text-base font-extrabold text-cyan-200"
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
                      <div className="text-xs font-semibold leading-4 text-slate-100">{item.label}</div>
                      <div className="mt-1 text-xs leading-4 text-slate-500">Ex: {item.example}</div>
                    </div>
                  ))}
                </div>
                <div className="mt-3 text-center text-xs font-medium uppercase text-slate-500">Workflows</div>
              </div>
            </div>
          </div>
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
        <div className="rounded-xl border border-slate-800 bg-slate-900/70 p-5 sm:p-8">
          <div className="max-w-3xl">
            <p className={eyebrowClass}>Reusable Workflow Marketplace</p>
            <h2 className={sectionTitleClass}>
              Package engineering know-how into reusable chip design products.
            </h2>
            <p className={sectionBodyClass}>
              ChipLoop turns individual agents and workflows into private apps, product journeys, and marketplace-ready solutions that other teams can run without rebuilding the environment.
            </p>
          </div>
          <div className="mt-8 grid grid-cols-1 gap-3 md:grid-cols-[1fr_auto_1fr_auto_1fr_auto_1fr_auto_1fr] md:items-stretch">
            {marketplaceFlow.map(([title, body], index) => (
              <div key={title} className="contents">
                <article className="rounded-xl border border-slate-800 bg-slate-950/70 p-4 text-center">
                  <div className={cardTitleClass}>{title}</div>
                  <p className={cardBodyClass}>{body}</p>
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
        </div>
      </section>

      <section className="w-full border-y border-slate-800 bg-slate-800/30 px-4 py-10 sm:px-6 sm:py-14">
        <div className={landingShellClass}>
        <div className="text-center">
          <h2 className={`${sectionTitleClass} mx-auto`}>Design Intent to Execution</h2>
          <p className={`${sectionBodyClass} mx-auto`}>
            ChipLoop turns complex multi-dimensional chip design workflows into connected, traceable execution loops.
          </p>
        </div>
        <div className="mt-8 grid grid-cols-1 items-stretch gap-4 md:grid-cols-[1fr_auto_1fr_auto_1fr]">
          {executionSteps.map(({ step, title, body, icon: Icon }, index) => (
            <div key={title} className="contents">
              <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-6 text-center">
                <div className="mx-auto flex h-10 w-10 items-center justify-center rounded-full bg-cyan-400 text-sm font-extrabold text-slate-950">
                  {step}
                </div>
                <Icon className="mx-auto mt-4 h-10 w-10 text-amber-300" aria-hidden="true" />
                <h3 className="mt-4 text-xl font-bold text-white">{title}</h3>
                <p className="mt-2 text-sm leading-6 text-slate-300">{body}</p>
              </div>
              {index < 2 ? (
                <div className="flex items-center justify-center text-3xl font-extrabold text-white md:px-2">
                  <span className="hidden md:inline">→</span>
                  <span className="md:hidden">↓</span>
                </div>
              ) : null}
            </div>
          ))}
        </div>
        </div>
      </section>

      <section className="w-full bg-slate-900/20 px-4 py-10 sm:px-6 sm:py-14">
        <div className="mx-auto max-w-[1440px]">
        <div className="rounded-xl border border-slate-800 bg-slate-900/80 p-5 sm:p-8 md:p-10">
          <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr] lg:items-center">
            <div>
              <p className={eyebrowClass}>Developer Automation</p>
              <h2 className={sectionTitleClass}>Automate from CLI, SDK, IDE, or GitHub</h2>
              <p className={sectionBodyClass}>
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
              <p className="mt-4 text-sm text-slate-400">Available for scripted, local, and CI-driven workflows.</p>
            </div>
            <div className="overflow-hidden rounded-xl border border-slate-700 bg-slate-950 shadow-2xl">
              <div className="flex items-center justify-between border-b border-slate-800 px-4 py-3">
                <div className="flex gap-2">
                  <span className="h-3 w-3 rounded-full bg-red-400" />
                  <span className="h-3 w-3 rounded-full bg-yellow-400" />
                  <span className="h-3 w-3 rounded-full bg-emerald-400" />
                </div>
                <div className="text-xs font-medium uppercase text-slate-500">
                  {automationSnippets[automationMode][automationStep].title}
                </div>
              </div>
              <pre className="min-h-36 overflow-x-auto whitespace-pre-wrap break-words px-4 py-4 text-left text-xs leading-6 text-slate-200 sm:min-h-44 sm:px-5 sm:py-5 sm:text-sm sm:leading-7">
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
        </div>
      </section>

      <section className="w-full border-t border-slate-800 bg-slate-800/30 px-4 py-12 text-center sm:px-6 sm:py-16">
        <div className="mx-auto max-w-5xl">
        <h2 className={`${sectionTitleClass} mx-auto`}>Start Building Connected Chip Workflows</h2>
        <p className={`${sectionBodyClass} mx-auto`}>
          Begin with the guided Arch2RTL demo, then continue through Products, Apps, or Studio.
        </p>
        <div className="mt-8 flex flex-col justify-center gap-4 sm:flex-row sm:flex-wrap">
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
        </div>
      </section>

      <footer className="border-t border-slate-800 bg-slate-950 px-6 py-8 text-center text-base text-slate-500">
        <div className="mb-4 flex flex-wrap justify-center gap-4 text-slate-400">
          <button onClick={() => router.push("/events")} className="hover:text-cyan-200">Events</button>
          <button onClick={() => router.push("/help")} className="hover:text-cyan-200">Playbook</button>
          <button onClick={() => router.push("/why-chiploop")} className="hover:text-cyan-200">Why ChipLoop</button>
          <button onClick={() => router.push("/webinar/register")} className="hover:text-cyan-200">Webinar</button>
          <button onClick={() => router.push("/contact")} className="hover:text-cyan-200">Contact Us</button>
        </div>
        <p className="mb-2 text-slate-300">Connect with us: chiploop.agx@gmail.com</p>
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
