"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { apiPost } from "@/lib/apiClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import GitHubImportPanel from "@/components/GitHubImportPanel";
import NextWorkflowLauncher from "@/components/NextWorkflowLauncher";
import SpecTextBox from "@/components/SpecTextBox";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  GENERIC_VERIFY_INTENT,
  IMAGE_VERIFY_INTENT,
  PWM_VERIFY_INTENT,
  SAFETY_VERIFY_INTENT,
  SECURE_BOOT_VERIFY_INTENT,
  SENSOR_VERIFY_INTENT,
  UART_VERIFY_INTENT,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const ONBOARDING_DEMO_KEY = "chiploop_arch2rtl_onboarding_demo";
const ARCH2RTL_HANDOFF_KEY = "chiploop_arch2rtl_handoff_prefill";

const ARCH2RTL_ONBOARDING_SPEC = `Design a parameterized PWM controller.

Inputs:
- clk
- reset_n
- enable
- duty_cycle[7:0]
- period[7:0]

Outputs:
- pwm_out
- counter_value[7:0]

Behavior:
- Counter increments every clock when enable is high.
- Counter resets to zero when it reaches period.
- pwm_out is high when counter_value is less than duty_cycle.
- All registers reset to zero when reset_n is low.

Generate synthesizable SystemVerilog, timing constraints, UPF-lite power intent, and a handoff package.`;

const ARCH2RTL_ONBOARDING_DEFAULTS = {
  projectName: "pwm_controller_onboarding",
  topModule: "pwm_controller",
  designLanguage: "systemverilog" as const,
  specText: ARCH2RTL_ONBOARDING_SPEC,
  toggles: { genRegmap: true, genUpfLite: true, genPackaging: true, insertMbist: false, mbistAlgorithm: "march-c" },
};

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type DemoUsage = {
  limit: number;
  runs_used: number;
  runs_remaining: number;
  can_run: boolean;
};

type TrialPrompt = {
  message: string;
  runsRemaining?: number;
  blocking?: boolean;
  checkoutUrl?: string;
  checkoutLabel?: string;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map(l => l.trimEnd()).filter(l => l.trim().length > 0);
}

export default function Arch2RTLAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [guidedOnboarding, setGuidedOnboarding] = useState(false);
  const [systemHandoff, setSystemHandoff] = useState(false);
  const [pwmChainDemo, setPwmChainDemo] = useState(false);
  const [uartChainDemo, setUartChainDemo] = useState(false);
  const [imageChainDemo, setImageChainDemo] = useState(false);
  const [mbistChainDemo, setMbistChainDemo] = useState(false);
  const [sensorChainDemo, setSensorChainDemo] = useState(false);
  const [secureChainDemo, setSecureChainDemo] = useState(false);
  const [safetyChainDemo, setSafetyChainDemo] = useState(false);
  const [onboardingCompleted, setOnboardingCompleted] = useState(false);
  const [trialPrompt, setTrialPrompt] = useState<TrialPrompt | null>(null);
  const [pendingTrialPrompt, setPendingTrialPrompt] = useState<TrialPrompt | null>(null);

  // Intake
  const [projectName, setProjectName] = useState("");
  const [topModule, setTopModule] = useState("");
  const [designLanguage, setDesignLanguage] = useState<"systemverilog" | "verilog">("systemverilog");
  const [specText, setSpecText] = useState("");

  const [genRegmap, setGenRegmap] = useState(true);
  const [genUpfLite, setGenUpfLite] = useState(false);
  const [genPackaging, setGenPackaging] = useState(true);
  const [runSpec2RtlCheck, setRunSpec2RtlCheck] = useState(false);
  const [insertMbist, setInsertMbist] = useState(false);
  const [mbistAlgorithm, setMbistAlgorithm] = useState<"march-c" | "march-raw">("march-c");

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const arch2rtlReady = useMemo(() => {
    if (workflowRow?.status === "completed") return true;
    return logLines.some((line) =>
      line.includes("Digital Arch2RTL Dashboard Agent done") ||
      line.includes("Digital App complete: arch2rtl")
    );
  }, [logLines, workflowRow?.status]);
  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  useEffect(() => {
    if (pendingTrialPrompt && workflowRow?.status === "completed") {
      setTrialPrompt(pendingTrialPrompt);
      setPendingTrialPrompt(null);
    }
  }, [pendingTrialPrompt, workflowRow?.status]);

  function authHeaders(): HeadersInit {
    const h: Record<string, string> = {};
    if (sessionUserId) h["x-user-id"] = sessionUserId;
    if (accessToken) h["Authorization"] = `Bearer ${accessToken}`;
    return h;
  }

  async function postJSON<T>(path: string, body: unknown): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...authHeaders() },
      body: JSON.stringify(body),
    });
    const text = await resp.text().catch(() => "");
    let data: unknown = null;
    try {
      data = text ? JSON.parse(text) : null;
    } catch {
      data = { detail: text };
    }
    if (!resp.ok) {
      const detail = data && typeof data === "object" ? (data as Record<string, unknown>).detail : data;
      const detailObject = detail && typeof detail === "object" ? (detail as Record<string, unknown>) : null;
      const message =
        (detailObject && typeof detailObject.message === "string" ? detailObject.message : null) ||
        (typeof detail === "string" ? detail : null) ||
        `${resp.status} ${resp.statusText}`;
      const error = new Error(message) as Error & { status?: number; payload?: unknown };
      error.status = resp.status;
      error.payload = data;
      throw error;
    }
    return data as T;
  }

  // Auth gate
  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        const next = typeof window !== "undefined"
          ? `${window.location.pathname}${window.location.search}`
          : "/apps/arch2rtl";
        router.replace(`/login?next=${encodeURIComponent(next)}`);
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const handoff = new URLSearchParams(window.location.search).get("handoff") === "system";
    if (handoff) {
      const rawHandoff = window.localStorage.getItem(ARCH2RTL_HANDOFF_KEY);
      if (rawHandoff) {
        try {
          const parsed = JSON.parse(rawHandoff) as Partial<typeof ARCH2RTL_ONBOARDING_DEFAULTS>;
          setSystemHandoff(true);
          setProjectName(parsed.projectName || "system_architecture_to_rtl");
          setTopModule(parsed.topModule || "system_architecture_wrapper");
          setDesignLanguage(parsed.designLanguage || "systemverilog");
          setSpecText(parsed.specText || "");
          setGenRegmap(parsed.toggles?.genRegmap ?? true);
          setGenUpfLite(parsed.toggles?.genUpfLite ?? true);
          setGenPackaging(parsed.toggles?.genPackaging ?? true);
          setMbistAlgorithm(parsed.toggles?.mbistAlgorithm === "march-raw" ? "march-raw" : "march-c");
          window.localStorage.removeItem(ARCH2RTL_HANDOFF_KEY);
          return;
        } catch {
          window.localStorage.removeItem(ARCH2RTL_HANDOFF_KEY);
        }
      }
    }
    const guided = new URLSearchParams(window.location.search).get("guided") === "1";
    if (!guided) return;

    setGuidedOnboarding(true);
    const params = new URLSearchParams(window.location.search);
    setPwmChainDemo(params.get("pwm_chain") === "1");
    setUartChainDemo(params.get("uart_chain") === "1");
    setImageChainDemo(params.get("image_chain") === "1");
    setMbistChainDemo(params.get("mbist_chain") === "1");
    setSensorChainDemo(params.get("sensor_chain") === "1");
    setSecureChainDemo(params.get("secure_chain") === "1");
    setSafetyChainDemo(params.get("safety_chain") === "1");
    let demo = ARCH2RTL_ONBOARDING_DEFAULTS;
    const raw = window.localStorage.getItem(ONBOARDING_DEMO_KEY);

    if (raw) {
      try {
        const parsed = JSON.parse(raw) as Partial<typeof ARCH2RTL_ONBOARDING_DEFAULTS>;
        demo = {
          ...ARCH2RTL_ONBOARDING_DEFAULTS,
          ...parsed,
          toggles: { ...ARCH2RTL_ONBOARDING_DEFAULTS.toggles, ...parsed.toggles },
        };
      } catch {
        window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
      }
    }

    setProjectName(demo.projectName);
    setTopModule(demo.topModule);
    setDesignLanguage(demo.designLanguage);
    setSpecText(demo.specText);
    setGenRegmap(demo.toggles.genRegmap);
    setGenUpfLite(demo.toggles.genUpfLite);
    setGenPackaging(demo.toggles.genPackaging);
    setInsertMbist(demo.toggles.insertMbist ?? false);
    setMbistAlgorithm(demo.toggles.mbistAlgorithm === "march-raw" ? "march-raw" : "march-c");
  }, [loading]);

  // Live workflow updates
  useEffect(() => {
    if (!workflowId) return;

    let isActive = true;

    const fetchWorkflow = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .single();

      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
    };

    void fetchWorkflow();
    const interval = window.setInterval(() => {
      void fetchWorkflow();
    }, 2500);

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
        (payload) => {
          const row = payload.new as Partial<WorkflowRow>;
          setWorkflowRow({
            id: row.id || workflowId,
            status: row.status,
            phase: row.phase,
            logs: row.logs,
            updated_at: row.updated_at,
          });
        }
      )
      .subscribe();

    return () => {
      isActive = false;
      window.clearInterval(interval);
      supabase.removeChannel(channel);
    };
  }, [workflowId]);

  const canRun = useMemo(() => {
    if (running) return false;
    if (!specText.trim()) return false;
    if (!topModule.trim()) return false;
    return true;
  }, [running, specText, topModule]);

  async function runNow() {
    setErr(null);
    setTrialPrompt(null);
    setPendingTrialPrompt(null);
    setRunning(true);
    try {
      const out = await postJSON<{
        ok: boolean;
        workflow_id: string;
        run_id: string;
        demo?: DemoUsage;
        trial_cta?: { show?: boolean; message?: string };
      }>(
        "/apps/arch2rtl/run",
        {
          project_name: projectName || undefined,
          top_module: topModule,
          design_language: designLanguage,
          spec_text: specText,
          toggles: {
            gen_regmap: genRegmap,
            gen_upf_lite: genUpfLite,
            gen_packaging: genPackaging,
            run_spec2rtl_check: runSpec2RtlCheck,
            insert_mbist: insertMbist,
            mbist_algorithm: mbistAlgorithm,
          },
        }
      );
      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
      if (out.trial_cta?.show) {
        setPendingTrialPrompt({
          message: out.trial_cta.message || "Start your 3-day trial to run your own specs. No charge today.",
          runsRemaining: out.demo?.runs_remaining,
          blocking: false,
        });
      }
      if (guidedOnboarding) {
        apiPost("/settings/onboarding", {
          action: "start",
          last_step: "arch2rtl_workflow_started",
          workflow_id: out.workflow_id,
          metadata: { demo: "arch2rtl" },
        }).catch(() => undefined);
      }
    } catch (e: unknown) {
      const error = e as Error & { status?: number; payload?: unknown };
      const payload = error.payload && typeof error.payload === "object" ? (error.payload as Record<string, unknown>) : null;
      const detail = payload?.detail && typeof payload.detail === "object" ? (payload.detail as Record<string, unknown>) : null;
      if (error.status === 402 && detail?.requires_checkout) {
        setTrialPrompt({
          message:
            typeof detail.message === "string"
              ? detail.message
              : "Start your 3-day trial to keep using ChipLoop.",
          checkoutUrl: typeof detail.checkout_url === "string" ? detail.checkout_url : "/pricing?trial=1",
          checkoutLabel: typeof detail.checkout_label === "string" ? detail.checkout_label : "Start 3-day trial",
          blocking: true,
        });
        setErr(null);
      } else {
        setErr(e instanceof Error ? e.message : String(e));
      }
    } finally {
      setRunning(false);
    }
  }

  async function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
    if (guidedOnboarding) {
      try {
        await apiPost("/settings/onboarding", {
          action: "complete",
          workflow_id: workflowId,
          last_step: "downloaded_artifacts",
          metadata: { demo: "arch2rtl", reviewed_files: ["rtl/*.sv", "constraints/*.sdc", "power/*.upf"] },
        });
        setOnboardingCompleted(true);
        window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
      } catch {
        setOnboardingCompleted(true);
      }
    }
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loading...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-[1600px] px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">
            Studio
          </button>
        </div>

        {guidedOnboarding ? (
          <div className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/20 p-5">
            <div className="flex flex-wrap items-start justify-between gap-4">
              <div>
                <div className="text-sm font-semibold uppercase tracking-wide text-cyan-300">Guided first activity</div>
                <h2 className="mt-1 text-2xl font-bold text-white">
                  {pwmChainDemo ? "Generate the PWM controller RTL" : uartChainDemo ? "Generate the UART packet engine RTL" : imageChainDemo ? "Generate the image DMA pipeline RTL" : mbistChainDemo ? "Generate the SRAM MBIST demo RTL" : sensorChainDemo ? "Generate the smart sensor hub MCU RTL" : secureChainDemo ? "Generate the secure boot key manager RTL" : safetyChainDemo ? "Generate the safety fault manager RTL" : "Run Arch2RTL and inspect the handoff package"}
                </h2>
                <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                  {pwmChainDemo
                    ? "The PWM controller specification is filled in for the connected RTL, firmware, and software demonstration. Run it to produce the RTL and register-map handoff used by the next stage."
                    : uartChainDemo
                    ? "The UART packet engine specification is filled in for a larger connected RTL, firmware, software, validation, and product-app demonstration. Run it to produce FIFO, UART, register, and interrupt collateral for the next stage."
                    : imageChainDemo
                    ? "The image DMA pipeline specification is filled in for a large visual connected demo. Run it to produce DMA, line-buffer, filter, histogram, interrupt, and register collateral for the next stage."
                    : mbistChainDemo
                    ? "The SRAM MBIST demo specification is filled in for a focused memory and DFT journey. Run it to produce a small SRAM controller, then open Synthesis to inspect scan, ATPG readiness, and MBIST applicability evidence."
                    : sensorChainDemo
                    ? "The smart sensor hub MCU specification is filled in for an IoT connected demo. Run it to produce sensor telemetry, FIFO, alert, low-power, interrupt, and register collateral for the next stage."
                    : secureChainDemo
                    ? "The secure boot/key manager specification is filled in for a root-of-trust demo. Run it to produce boot authentication, key-slot, anti-rollback, debug-lock, tamper, and audit collateral for the next stage."
                    : safetyChainDemo
                    ? "The safety fault manager specification is filled in for an automotive safety demo. Run it to produce watchdog, fault-mask, escalation, reset-request, IRQ, and diagnostic collateral for the next stage."
                    : "The PWM controller spec is already filled in. Click Run Arch2RTL, wait for logs to finish, then download the ZIP and inspect the RTL, SDC, and UPF files."}
                </p>
              </div>
              {onboardingCompleted ? (
                <span className="rounded-full border border-emerald-700 bg-emerald-950/40 px-3 py-1 text-sm text-emerald-100">
                  Completed
                </span>
              ) : null}
            </div>
            <div className="mt-4 grid gap-3 md:grid-cols-4">
              {[
                safetyChainDemo ? "Review pre-filled safety fault spec" : secureChainDemo ? "Review pre-filled secure boot spec" : sensorChainDemo ? "Review pre-filled sensor hub spec" : mbistChainDemo ? "Review pre-filled SRAM MBIST spec" : imageChainDemo ? "Review pre-filled image DMA spec" : uartChainDemo ? "Review pre-filled UART packet spec" : "Review pre-filled PWM spec",
                "Run Arch2RTL",
                "Open the downloaded RTL, SDC, and UPF files",
                "Download ZIP to complete onboarding",
              ].map((item, idx) => (
                <div key={item} className="rounded-xl border border-slate-800 bg-black/25 p-3 text-sm text-slate-200">
                  <div className="mb-2 flex h-7 w-7 items-center justify-center rounded-full bg-cyan-600 text-xs font-bold">{idx + 1}</div>
                  {item}
                </div>
              ))}
            </div>
          </div>
        ) : null}

        {systemHandoff ? (
          <div className="mt-6 rounded-2xl border border-emerald-900/60 bg-emerald-950/20 p-5">
            <div className="text-sm font-semibold uppercase tracking-wide text-emerald-300">System Architecture handoff</div>
            <h2 className="mt-1 text-2xl font-bold text-white">Review RTL intent from gem5 architecture evidence</h2>
            <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
              This spec was generated from a completed System Architecture run. Review the selected parameters and traceability notes, then run Arch2RTL when the scope matches the RTL you want.
            </p>
          </div>
        ) : null}

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Arch2RTL</h1>
          <p className="mt-2 text-slate-300">One-shot intake to one click run to progressive outputs to ZIP handoff.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input value={projectName} onChange={e => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Top module *</label>
              <input value={topModule} onChange={e => setTopModule(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Design language</label>
              <select value={designLanguage} onChange={e => setDesignLanguage(e.target.value as "systemverilog" | "verilog")}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                <option value="systemverilog">SystemVerilog</option>
                <option value="verilog">Verilog</option>
              </select>

              <div className="mt-3 space-y-2">
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genRegmap} onChange={e => setGenRegmap(e.target.checked)} />
                  Generate regmap
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genUpfLite} onChange={e => setGenUpfLite(e.target.checked)} />
                  Generate UPF-lite
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genPackaging} onChange={e => setGenPackaging(e.target.checked)} />
                  Generate packaging/handoff
                </label>
                <label className="flex items-start gap-2 text-sm text-slate-300">
                  <input className="mt-1" type="checkbox" checked={runSpec2RtlCheck} onChange={e => setRunSpec2RtlCheck(e.target.checked)} />
                  <span>
                    Run Spec-to-RTL conformance check
                    <span className="block text-xs text-slate-500">
                      Optional: checks generated RTL against spec, interfaces, reset behavior, register intent, and requirement trace.
                    </span>
                  </span>
                </label>
                <label className="flex items-start gap-2 text-sm text-slate-300">
                  <input className="mt-1" type="checkbox" checked={insertMbist} onChange={e => setInsertMbist(e.target.checked)} />
                  <span>
                    Insert MBIST
                    <span className="block text-xs text-slate-500">
                      Optional: only runs when OpenRAM/SRAM is detected. AutoMBIST wrapper simulation must pass before RTL handoff is updated.
                    </span>
                  </span>
                </label>
                {insertMbist ? (
                  <label className="block text-sm text-slate-300">
                    MBIST algorithm
                    <select
                      value={mbistAlgorithm}
                      onChange={e => setMbistAlgorithm(e.target.value === "march-raw" ? "march-raw" : "march-c")}
                      className="mt-1 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    >
                      <option value="march-c">March C</option>
                      <option value="march-raw">March Raw</option>
                    </select>
                    <span className="mt-1 block text-xs text-slate-500">
                      AutoMBIST default is March C. March Raw is available for raw March algorithm collateral.
                    </span>
                  </label>
                ) : null}
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting..." : "Run Arch2RTL"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

              {trialPrompt ? (
                <div className={`mt-4 rounded-xl border p-4 text-sm ${
                  trialPrompt.blocking
                    ? "border-amber-700 bg-amber-950/30 text-amber-100"
                    : "border-cyan-800 bg-cyan-950/20 text-cyan-100"
                }`}>
                  <div className="font-semibold">
                    {trialPrompt.blocking ? "Trial required to continue" : "Ready to run your own spec?"}
                  </div>
                  <div className="mt-1 leading-6 text-slate-200">{trialPrompt.message}</div>
                  {typeof trialPrompt.runsRemaining === "number" ? (
                    <div className="mt-1 text-xs text-slate-400">
                      Demo runs remaining: {trialPrompt.runsRemaining}
                    </div>
                  ) : null}
                  <button
                    type="button"
                    onClick={() => router.push(trialPrompt.checkoutUrl || "/pricing?trial=1")}
                    className="mt-3 rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500"
                  >
                    {trialPrompt.checkoutLabel || "Start 3-day trial"}
                  </button>
                </div>
              ) : null}
            </div>

            <div>
              <SpecTextBox
                label="Spec text"
                required
                value={specText}
                onChange={setSpecText}
                rows={18}
                voiceTitle="Voice Spec Draft"
                voiceLoopType="digital"
                voiceTarget="Digital spec"
                uploadLabel="Upload spec"
                uploadHelper="Load a text, markdown, JSON, YAML, SystemVerilog, Verilog, or SDC spec file."
                placeholder="Paste your spec here..."
              />
              <div className="mt-3">
                <GitHubImportPanel
                  compact
                  onImport={(importedText) => {
                    setSpecText((current) => [current.trim(), importedText.trim()].filter(Boolean).join("\n\n"));
                  }}
                />
              </div>
              <div className="mt-2 text-xs text-slate-500">Tip: keep it structured (interfaces, clocks, resets, targets).</div>
            </div>
          </div>

          {workflowId ? (
            <div className="mt-6 space-y-4">
              <div className="rounded-2xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                <div className="font-semibold text-slate-100">Run Status</div>
                <div className="mt-2">
                  workflow_id: <span className="break-all text-slate-100">{workflowId}</span>
                </div>
                <div className="mt-1">
                  run_id: <span className="break-all text-slate-100">{runId}</span>
                </div>
                <div className="mt-1">
                  status: <span className="text-slate-100">{arch2rtlReady ? "completed" : workflowRow?.status || "queued"}</span>
                </div>
                <div className="mt-3 flex flex-wrap gap-2">
                  <button onClick={downloadZip} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                    {guidedOnboarding ? "Download ZIP and finish" : "Download ZIP (full=1)"}
                  </button>
                </div>
                <div className="mt-4">
                  <NextWorkflowLauncher
                    currentStage="arch2rtl"
                    currentWorkflowId={workflowId}
                    currentRunId={runId}
                    sourceArch2RTLWorkflowId={workflowId}
                    disabled={!arch2rtlReady}
                    verifyTestIntent={pwmChainDemo ? PWM_VERIFY_INTENT : uartChainDemo ? UART_VERIFY_INTENT : imageChainDemo ? IMAGE_VERIFY_INTENT : mbistChainDemo ? `Verify the SRAM MBIST demo controller generated by Arch2RTL.

Directed scenarios:
- Reset the controller and confirm ready, BIST status, IRQ, and memory read data clear.
- Write and read several SRAM addresses through the memory-mapped interface.
- Start the BIST path and confirm bist_done, bist_fail, and IRQ status behavior.
- Exercise IRQ_CLEAR and BIST_CONTROL.CLEAR_RESULT.

Collect register readback, memory access, BIST status, assertion, and coverage evidence.` : sensorChainDemo ? SENSOR_VERIFY_INTENT : secureChainDemo ? SECURE_BOOT_VERIFY_INTENT : safetyChainDemo ? SAFETY_VERIFY_INTENT : GENERIC_VERIFY_INTENT}
                    verifyCoverageTargets={
                      pwmChainDemo
                        ? "PWM duty-cycle scenarios, reset behavior, dynamic updates"
                        : uartChainDemo
                        ? "UART packet movement, FIFO levels, interrupt status, framing and overflow error handling"
                        : imageChainDemo
                        ? "DMA progress, line-buffer windows, filter modes, histogram bins, frame_done interrupt behavior"
                        : mbistChainDemo
                        ? "SRAM register access, BIST start/done/fail behavior, IRQ clear, memory wrapper interface"
                        : sensorChainDemo
                        ? "Sensor sampling, FIFO levels, threshold alerts, interrupt clear, low-power behavior"
                        : secureChainDemo
                        ? "Boot authentication, key-slot coverage, rollback, tamper, debug lock, security IRQ behavior"
                        : safetyChainDemo
                        ? "Watchdog heartbeat, timeout, fault masks, escalation, reset request, safety IRQ behavior"
                        : "Derived interface behavior, reset behavior, functional corner cases"
                    }
                    verifyQuerySuffix={`${pwmChainDemo ? "&pwm_chain=1" : ""}${uartChainDemo ? "&uart_chain=1" : ""}${imageChainDemo ? "&image_chain=1" : ""}${mbistChainDemo ? "&mbist_chain=1" : ""}${sensorChainDemo ? "&sensor_chain=1" : ""}${secureChainDemo ? "&secure_chain=1" : ""}${safetyChainDemo ? "&safety_chain=1" : ""}`}
                  />
                </div>
              </div>

              <WorkflowEvidenceDashboard workflowId={workflowId} status={arch2rtlReady ? "completed" : workflowRow?.status} stage="arch2rtl" logs={workflowRow?.logs} />
            </div>
          ) : null}

          {workflowId ? (
            <div className="mt-6">
              <AskThisRunPanel workflowId={workflowId} compact />
            </div>
          ) : null}

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((l, i) => <div key={i} className="whitespace-pre-wrap">{l}</div>) : (
                <div className="text-slate-500">No logs yet. Click Run Arch2RTL.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}





