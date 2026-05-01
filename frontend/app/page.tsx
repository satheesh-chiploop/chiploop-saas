"use client";

import { Suspense, useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

const loops = [
  "Digital",
  "Embedded",
  "Software",
  "Validation",
  "Analog",
  "Physical Design",
  "System",
  "Still exploring",
];

const automationSnippets = {
  cli: [
    {
      title: "Install",
      code: "pip install chiploop-sdk",
    },
    {
      title: "Check setup",
      code: "chiploop doctor",
    },
    {
      title: "Run Arch2RTL",
      code: "chiploop run arch2rtl --spec spec.md",
    },
    {
      title: "Download artifacts",
      code: "chiploop artifacts download <workflow_id> --name rtl/top.v --out ./outputs",
    },
  ],
  sdk: [
    {
      title: "Create client",
      code: "from chiploop_sdk import ChipLoopClient\n\nclient = ChipLoopClient()",
    },
    {
      title: "Run workflow",
      code: "run = client.run_workflow(\n    \"arch2rtl\",\n    spec_text=\"Create a PWM controller.\"\n)",
    },
    {
      title: "Check status",
      code: "status = client.get_workflow_status(run.workflow_id)\nprint(status.status)",
    },
    {
      title: "List artifacts",
      code: "artifacts = client.list_artifacts(run.workflow_id)\nprint(artifacts)",
    },
  ],
  ide: [
    {
      title: "VS Code",
      code: "ChipLoop: Configure\nChipLoop: Run Arch2RTL",
    },
    {
      title: "Current file",
      code: "Open specs/pwm.md\nRun: ChipLoop: Run Workflow from Current File",
    },
    {
      title: "Artifacts",
      code: "ChipLoop: Check Workflow Status\nChipLoop: Download Artifacts",
    },
    {
      title: "Cursor",
      code: "Use the Cursor terminal:\nchiploop run arch2rtl --spec specs/pwm.md",
    },
  ],
  github: [
    {
      title: "Action",
      code: "uses: ./backend/integrations/github-action\nwith:\n  workflow: arch2rtl\n  spec: specs/pwm.md",
    },
    {
      title: "Secrets",
      code: "CHIPLOOP_BASE_URL\nCHIPLOOP_API_KEY",
    },
    {
      title: "Outputs",
      code: "Upload generated RTL, SDC, UPF, and reports\nas GitHub workflow artifacts",
    },
    {
      title: "Review",
      code: "Run ChipLoop on PR specs\nReview artifacts before merging",
    },
  ],
};

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

  const goToApps = async () => {
    setLoginLoading(true);
    if (userEmail) {
      router.push("/apps");
      return;
    }
    const {
      data: { session },
    } = await supabase.auth.getSession();
    if (session) {
      router.push("/apps");
      return;
    }
    router.push("/login?next=/apps");
  };

  const startGuidedDemo = async () => {
    setLoginLoading(true);
    const next = "/apps/arch2rtl?guided=1";
    const {
      data: { session },
    } = await supabase.auth.getSession();
    router.push(session ? next : `/login?next=${encodeURIComponent(next)}`);
  };

  if (loginLoading) {
    return (
      <main className="min-h-screen flex items-center justify-center bg-slate-950 text-white">
        <div className="text-slate-300">Redirecting...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <nav className="fixed left-0 top-0 z-50 w-full border-b border-slate-800 bg-slate-950/90 backdrop-blur">
        <div className="mx-auto flex max-w-7xl items-center justify-between px-6 py-4">
          <button onClick={() => router.push("/")} className="text-xl font-extrabold text-cyan-300">
            ChipLoop
          </button>
          <div className="hidden items-center gap-7 text-sm font-medium text-slate-300 md:flex">
            <button onClick={() => router.push("/apps")} className="hover:text-cyan-300">Apps</button>
            <button onClick={() => router.push("/workflow")} className="hover:text-cyan-300">Studio</button>
            <button onClick={() => router.push("/marketplace")} className="hover:text-cyan-300">Marketplace</button>
            <button onClick={() => router.push("/pricing")} className="hover:text-cyan-300">Pricing</button>
            <button onClick={() => router.push("/webinar/register")} className="hover:text-cyan-300">Webinar</button>
            {!userEmail ? (
              <button onClick={() => router.push("/login?next=/apps")} className="hover:text-cyan-300">Login</button>
            ) : null}
          </div>
          <div className="flex items-center gap-3">
            {userEmail ? (
              <button
                onClick={async () => {
                  await supabase.auth.signOut();
                  setUserEmail(null);
                  router.push("/");
                }}
                className="hidden rounded-lg border border-slate-700 px-4 py-2.5 text-sm font-semibold text-slate-300 transition hover:bg-slate-900 md:inline-flex"
              >
                Logout
              </button>
            ) : null}
            <button
              onClick={goToApps}
              className="rounded-lg bg-cyan-400 px-5 py-2.5 text-sm font-bold text-slate-950 transition hover:bg-cyan-300"
            >
              {userEmail ? "Enter Apps" : "Start Free Trial"}
            </button>
          </div>
        </div>
      </nav>

      <section className="mx-auto flex max-w-7xl flex-col items-center px-6 pb-16 pt-32 text-center">
        <div className="mb-5 rounded-full border border-cyan-400/30 bg-cyan-400/10 px-4 py-2 text-sm font-semibold text-cyan-200">
          Weekly live demo starts May 23, 2026
        </div>
        <h1 className="max-w-5xl text-5xl font-extrabold tracking-tight text-white md:text-7xl">
          Agentic AI for Connected Chip Design Loops
        </h1>
        <p className="mt-7 max-w-3xl text-lg leading-8 text-slate-300">
          Build chip workflows across Digital, Embedded, Software, Validation, Analog, and Physical Design in one platform.
          ChipLoop helps teams share specs, generated artifacts, and design context across loops instead of working in disconnected tools.
        </p>
        <div className="mt-10 flex flex-col gap-4 sm:flex-row">
          <button
            onClick={startGuidedDemo}
            className="rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 shadow-lg shadow-cyan-950/30 transition hover:bg-cyan-300"
          >
            Start Guided Arch2RTL Demo
          </button>
          <button
            onClick={() => router.push("/webinar/register")}
            className="rounded-xl border border-slate-600 px-7 py-3 font-bold text-white transition hover:border-cyan-300 hover:text-cyan-200"
          >
            Register for Saturday Webinar
          </button>
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-6 py-14">
        <div className="mb-8 text-center">
          <h2 className="text-3xl font-bold">One Platform. Many Chip Design Loops.</h2>
          <p className="mt-3 text-slate-400">Keep engineering context connected as work moves across loops.</p>
        </div>
        <div className="grid grid-cols-1 gap-5 md:grid-cols-3">
          {loops.slice(0, 6).map((loop) => (
            <div key={loop} className="rounded-xl border border-slate-800 bg-slate-900/70 p-6">
              <h3 className="text-xl font-bold text-cyan-300">{loop} Loop</h3>
              <p className="mt-3 text-sm leading-6 text-slate-300">
                Plan, generate, validate, and hand off artifacts while preserving shared design context.
              </p>
            </div>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-7xl px-6 py-14">
        <div className="grid grid-cols-1 gap-5 md:grid-cols-3">
          {[
            ["Connected Design Data", "Specs, generated files, reports, and workflow results stay connected across loops."],
            ["Agentic AI Workflows", "AI agents help plan, generate, validate, repair, and document chip design tasks."],
            ["Real Engineering Outputs", "Generate RTL, testbenches, firmware stubs, SDK files, SDC, UPF, reports, and reviewable artifacts."],
          ].map(([title, body]) => (
            <div key={title} className="rounded-xl bg-slate-900 p-6 ring-1 ring-slate-800">
              <h3 className="font-bold text-white">{title}</h3>
              <p className="mt-3 text-sm leading-6 text-slate-300">{body}</p>
            </div>
          ))}
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-6 py-14">
        <div className="rounded-2xl border border-cyan-400/30 bg-cyan-400/10 p-8 md:p-10">
          <div className="grid grid-cols-1 gap-8 md:grid-cols-[1.3fr_0.7fr] md:items-center">
            <div>
              <p className="text-sm font-bold uppercase tracking-wide text-cyan-200">Weekly ChipLoop Webinar</p>
              <h2 className="mt-3 text-3xl font-extrabold text-white">30-minute walkthrough and live demo every Saturday</h2>
              <p className="mt-4 leading-7 text-slate-300">
                Starting May 23, join at 9:00 AM PST or 9:00 PM PST. We will cover ChipLoop Apps, Studio, connected Loops,
                the guided Arch2RTL demo, generated RTL, SDC, UPF, downloadable artifacts, and Q&A.
              </p>
            </div>
            <div className="rounded-xl border border-slate-700 bg-slate-950/70 p-5">
              <div className="text-sm text-slate-400">Sessions</div>
              <div className="mt-2 font-semibold text-white">Saturday 9:00 AM PST</div>
              <div className="mt-1 font-semibold text-white">Saturday 9:00 PM PST</div>
              <button
                onClick={() => router.push("/webinar/register")}
                className="mt-5 w-full rounded-lg bg-cyan-400 px-5 py-3 font-bold text-slate-950 transition hover:bg-cyan-300"
              >
                Register for Webinar
              </button>
            </div>
          </div>
        </div>
      </section>

      <section className="mx-auto max-w-6xl px-6 py-14">
        <div className="rounded-2xl border border-slate-800 bg-slate-900/80 p-8 md:p-10">
          <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr] lg:items-center">
            <div>
              <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Developer Automation</p>
              <h2 className="mt-3 text-3xl font-extrabold text-white">Use ChipLoop from CLI, SDK, IDE, or GitHub</h2>
              <p className="mt-4 leading-7 text-slate-300">
                Start in Apps from the browser. When your workflow needs scripts, CI, local editor workflows, or repo automation,
                Pro, Pro Max, and Enterprise include developer automation access.
              </p>
              <div className="mt-6 flex flex-wrap gap-3">
                <button
                  onClick={() => setAutomationMode("cli")}
                  className={`rounded-lg px-4 py-2 text-sm font-bold transition ${
                    automationMode === "cli"
                      ? "bg-cyan-400 text-slate-950"
                      : "border border-slate-700 text-slate-300 hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  CLI
                </button>
                <button
                  onClick={() => setAutomationMode("sdk")}
                  className={`rounded-lg px-4 py-2 text-sm font-bold transition ${
                    automationMode === "sdk"
                      ? "bg-cyan-400 text-slate-950"
                      : "border border-slate-700 text-slate-300 hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  Python SDK
                </button>
                <button
                  onClick={() => setAutomationMode("ide")}
                  className={`rounded-lg px-4 py-2 text-sm font-bold transition ${
                    automationMode === "ide"
                      ? "bg-cyan-400 text-slate-950"
                      : "border border-slate-700 text-slate-300 hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  VS Code / Cursor
                </button>
                <button
                  onClick={() => setAutomationMode("github")}
                  className={`rounded-lg px-4 py-2 text-sm font-bold transition ${
                    automationMode === "github"
                      ? "bg-cyan-400 text-slate-950"
                      : "border border-slate-700 text-slate-300 hover:border-cyan-300 hover:text-cyan-200"
                  }`}
                >
                  GitHub
                </button>
                <button
                  onClick={() => router.push("/pricing")}
                  className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-300 transition hover:border-cyan-300 hover:text-cyan-200"
                >
                  View Pricing
                </button>
              </div>
              <p className="mt-4 text-sm text-slate-400">Developer automation is available on Pro, Pro Max, and Enterprise plans.</p>
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
              <pre className="min-h-44 whitespace-pre-wrap px-5 py-5 text-left text-sm leading-7 text-cyan-100">
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

      <section className="mx-auto max-w-5xl px-6 py-16 text-center">
        <h2 className="text-3xl font-extrabold">Start Building Connected Chip Workflows</h2>
        <p className="mt-4 text-slate-300">
          Begin with the guided Arch2RTL demo, then explore more Loops inside Apps and Studio.
        </p>
        <div className="mt-8 flex flex-col justify-center gap-4 sm:flex-row">
          <button onClick={startGuidedDemo} className="rounded-xl bg-cyan-400 px-7 py-3 font-bold text-slate-950 hover:bg-cyan-300">
            Run Guided Demo
          </button>
          <button onClick={goToApps} className="rounded-xl border border-slate-600 px-7 py-3 font-bold text-white hover:border-cyan-300">
            Explore Apps
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






