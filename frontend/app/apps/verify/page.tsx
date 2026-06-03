"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import VoiceSpecDraft from "@/components/VoiceSpecDraft";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import NextWorkflowLauncher from "@/components/NextWorkflowLauncher";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  EMBEDDED_HANDOFF_PREFILL_KEY,
  GENERIC_EMBEDDED_SPEC,
  IMAGE_EMBEDDED_SPEC,
  PWM_EMBEDDED_SPEC,
  SAFETY_EMBEDDED_SPEC,
  SECURE_BOOT_EMBEDDED_SPEC,
  SENSOR_EMBEDDED_SPEC,
  UART_EMBEDDED_SPEC,
  VERIFY_HANDOFF_PREFILL_KEY,
  type DesignChainContext,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs
    .split("\n")
    .map((l) => l.trimEnd())
    .filter((l) => l.trim().length > 0);
}

export default function VerifyAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [closureWorkflowId, setClosureWorkflowId] = useState<string | null>(null);
  const [closureRunId, setClosureRunId] = useState<string | null>(null);
  const [closureRow, setClosureRow] = useState<WorkflowRow | null>(null);

  // Intake (minimal but useful)
  const [rtlSourceMode, setRtlSourceMode] = useState<"from_arch2rtl" | "paste" | "repo_path">("repo_path");
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [parentWorkflowId, setParentWorkflowId] = useState("");
  const [upstreamWorkflows, setUpstreamWorkflows] = useState<Record<string, string>>({});
  const [repoPath, setRepoPath] = useState("");
  const [pastedRtl, setPastedRtl] = useState("");

  const [testIntent, setTestIntent] = useState("");
  const [randomVsDirected, setRandomVsDirected] = useState<"random" | "directed" | "both">("both");
  const [coverageTargets, setCoverageTargets] = useState("");
  const [simulatorType, setSimulatorType] = useState("verilator");
  const [codeCoverageTool, setCodeCoverageTool] = useState("verilator_coverage");
  const [formalTool, setFormalTool] = useState("none");
  const [formalSolver, setFormalSolver] = useState("z3");
  const [goldenModelTool, setGoldenModelTool] = useState("none");
  const [seedCount, setSeedCount] = useState<number>(10);
  const [runClosureAnalysis, setRunClosureAnalysis] = useState(true);
  const closureStartedRef = useRef(false);

  const [handoffFlow, setHandoffFlow] = useState(false);
  const [pwmChainDemo, setPwmChainDemo] = useState(false);
  const [uartChainDemo, setUartChainDemo] = useState(false);
  const [imageChainDemo, setImageChainDemo] = useState(false);
  const [sensorChainDemo, setSensorChainDemo] = useState(false);
  const [secureChainDemo, setSecureChainDemo] = useState(false);
  const [safetyChainDemo, setSafetyChainDemo] = useState(false);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  function authHeaders(): HeadersInit {
    const h: Record<string, string> = {};
    if (sessionUserId) h["x-user-id"] = sessionUserId;
    if (accessToken) h["Authorization"] = `Bearer ${accessToken}`;
    return h;
  }

  async function postJSON<T>(path: string, body: any): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...authHeaders() },
      body: JSON.stringify(body),
    });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` — ${txt}` : ""}`);
    }
    return resp.json();
  }

  // Auth gate
  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);

      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/verify");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    if (params.get("handoff") !== "1" && params.get("pwm_chain") !== "1" && params.get("uart_chain") !== "1" && params.get("image_chain") !== "1" && params.get("sensor_chain") !== "1" && params.get("secure_chain") !== "1" && params.get("safety_chain") !== "1") return;
    setHandoffFlow(true);
    setPwmChainDemo(params.get("pwm_chain") === "1");
    setUartChainDemo(params.get("uart_chain") === "1");
    setImageChainDemo(params.get("image_chain") === "1");
    setSensorChainDemo(params.get("sensor_chain") === "1");
    setSecureChainDemo(params.get("secure_chain") === "1");
    setSafetyChainDemo(params.get("safety_chain") === "1");
    const raw = window.localStorage.getItem(VERIFY_HANDOFF_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as {
        fromWorkflowId?: string;
        testIntent?: string;
        randomVsDirected?: "random" | "directed" | "both";
        coverageTargets?: string;
        simulatorType?: string;
        seedCount?: number;
        parentWorkflowId?: string;
        upstreamWorkflows?: Record<string, string>;
      };
      setRtlSourceMode("from_arch2rtl");
      setFromWorkflowId(prefill.fromWorkflowId || "");
      setTestIntent(prefill.testIntent || "");
      setRandomVsDirected(prefill.randomVsDirected || "both");
      setCoverageTargets(prefill.coverageTargets || "");
      setSimulatorType(prefill.simulatorType || "verilator");
      setCodeCoverageTool("verilator_coverage");
      setSeedCount(prefill.seedCount || 4);
      setParentWorkflowId(prefill.parentWorkflowId || "");
      setUpstreamWorkflows(prefill.upstreamWorkflows || {});
    } catch {
      window.localStorage.removeItem(VERIFY_HANDOFF_PREFILL_KEY);
    }
  }, [loading]);

  // Live workflow updates
  useEffect(() => {
    if (!workflowId) return;

    let isActive = true;

    (async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .single();

      if (isActive && !error && data) setWorkflowRow(data as any);
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
        (payload) => {
          const row = payload.new as any;
          setWorkflowRow({
            id: row.id,
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
      supabase.removeChannel(channel);
    };
  }, [workflowId]);

  useEffect(() => {
    if (!closureWorkflowId) return;

    let isActive = true;

    (async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", closureWorkflowId)
        .single();

      if (isActive && !error && data) setClosureRow(data as any);
    })();

    const channel = supabase
      .channel(`wf-${closureWorkflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${closureWorkflowId}` },
        (payload) => {
          const row = payload.new as any;
          setClosureRow({
            id: row.id,
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
      supabase.removeChannel(channel);
    };
  }, [closureWorkflowId]);

  useEffect(() => {
    if (!runClosureAnalysis || closureStartedRef.current) return;
    if (!workflowId || workflowRow?.status !== "completed") return;
    closureStartedRef.current = true;
    void analyzeClosure();
  }, [runClosureAnalysis, workflowId, workflowRow?.status]);

  const canRun = useMemo(() => {
    if (running) return false;

    // need rtl source and test intent
    if (!testIntent.trim()) return false;
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "from_arch2rtl" && !fromWorkflowId.trim()) return false;
    if (rtlSourceMode === "paste" && !pastedRtl.trim()) return false;

    // seed_count sanity
    if (!Number.isFinite(seedCount) || seedCount <= 0) return false;

    return true;
  }, [running, testIntent, rtlSourceMode, repoPath, fromWorkflowId, pastedRtl, seedCount]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    closureStartedRef.current = false;
    setClosureWorkflowId(null);
    setClosureRunId(null);
    setClosureRow(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/verify/run",
        {
          rtl_source_mode: rtlSourceMode,
          from_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
          source_arch2rtl_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
          parent_workflow_id: parentWorkflowId || undefined,
          upstream_workflows: rtlSourceMode === "from_arch2rtl" ? { ...upstreamWorkflows, arch2rtl: fromWorkflowId } : undefined,
          repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
          pasted_rtl_files:
            rtlSourceMode === "paste"
              ? [{ path: "rtl/top.sv", content: pastedRtl }]
              : undefined,

          test_intent: testIntent,
          random_vs_directed: randomVsDirected,
          coverage_targets: coverageTargets || undefined,
          simulator_type: simulatorType || undefined,
          seed_count: seedCount,
          toolchain: {
            simulator: simulatorType || "verilator",
            code_coverage: codeCoverageTool,
            formal: formalTool,
            formal_solver: formalSolver,
            golden_model: goldenModelTool,
          },
          run_closure_analysis: runClosureAnalysis,

          toggles: {
            enable_formal: formalTool !== "none",
            enable_golden_model: goldenModelTool !== "none",
          },
        }
      );

      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
    } catch (e: any) {
      setErr(e?.message || String(e));
    } finally {
      setRunning(false);
    }
  }

  async function analyzeClosure() {
    if (!workflowId) return;
    setErr(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/verify/closure/run",
        {
          source_verify_workflow_id: workflowId,
          coverage_targets: coverageTargets || undefined,
          seed_count: seedCount,
          toolchain: {
            simulator: simulatorType || "verilator",
            code_coverage: codeCoverageTool,
            formal: formalTool,
            formal_solver: formalSolver,
            golden_model: goldenModelTool,
          },
        }
      );
      setClosureWorkflowId(out.workflow_id);
      setClosureRunId(out.run_id);
    } catch (e: any) {
      closureStartedRef.current = false;
      setErr(e?.message || String(e));
    }
  }

  function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
  }

  function downloadClosureZip() {
    if (!closureWorkflowId) return;
    window.open(`${API_BASE}/workflow/${closureWorkflowId}/download_zip?full=1`, "_blank");
  }

  function openInEmbeddedFirmware() {
    if (!workflowId) return;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    const sourceArch2rtlWorkflowId = context.arch2rtlWorkflowId || fromWorkflowId || undefined;
    if (sourceArch2rtlWorkflowId) context.arch2rtlWorkflowId = sourceArch2rtlWorkflowId;
    context.verifyWorkflowId = workflowId;
    context.verifyRunId = runId || undefined;
    context.demoKind = pwmChainDemo ? "pwm" : uartChainDemo ? "uart_packet" : imageChainDemo ? "image_dma" : sensorChainDemo ? "sensor_hub" : secureChainDemo ? "secure_boot" : safetyChainDemo ? "safety_fault" : context.demoKind;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    window.localStorage.setItem(EMBEDDED_HANDOFF_PREFILL_KEY, JSON.stringify({
      specText: pwmChainDemo ? PWM_EMBEDDED_SPEC : uartChainDemo ? UART_EMBEDDED_SPEC : imageChainDemo ? IMAGE_EMBEDDED_SPEC : sensorChainDemo ? SENSOR_EMBEDDED_SPEC : secureChainDemo ? SECURE_BOOT_EMBEDDED_SPEC : safetyChainDemo ? SAFETY_EMBEDDED_SPEC : GENERIC_EMBEDDED_SPEC,
      goal: pwmChainDemo
        ? "Generate Rust firmware and validate its PWM interface against the imported RTL."
        : uartChainDemo
        ? "Generate Rust firmware and validate UART packet, FIFO, and interrupt behavior against the imported RTL."
        : imageChainDemo
        ? "Generate Rust firmware and validate image DMA, filter, histogram, and interrupt behavior against the imported RTL."
        : sensorChainDemo
        ? "Generate Rust firmware and validate sensor sampling, FIFO, alerts, and low-power behavior against the imported RTL."
        : secureChainDemo
        ? "Generate Rust firmware and validate secure boot, rollback, tamper, debug-lock, and security IRQ behavior against the imported RTL."
        : safetyChainDemo
        ? "Generate Rust firmware and validate watchdog heartbeat, fault handling, reset escalation, and safety IRQ behavior against the imported RTL."
        : "Generate firmware and validation collateral from the actual imported RTL and register map.",
      fromWorkflowId: sourceArch2rtlWorkflowId,
      fromRunId: context.arch2rtlRunId,
      sourceVerificationWorkflowId: workflowId,
      sourceVerificationRunId: runId,
      topModule: pwmChainDemo ? "pwm_controller" : uartChainDemo ? "uart_packet_engine" : imageChainDemo ? "image_dma_pipeline" : sensorChainDemo ? "smart_sensor_hub_mcu" : secureChainDemo ? "secure_boot_key_manager" : safetyChainDemo ? "safety_fault_watchdog" : undefined,
    }));
    router.push(`/apps/embedded-run?handoff=1${pwmChainDemo ? "&pwm_chain=1" : ""}${uartChainDemo ? "&uart_chain=1" : ""}${imageChainDemo ? "&image_chain=1" : ""}${sensorChainDemo ? "&sensor_chain=1" : ""}${secureChainDemo ? "&secure_chain=1" : ""}${safetyChainDemo ? "&safety_chain=1" : ""}`);
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loading…</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-6xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button
            onClick={() => router.push("/apps")}
            className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 transition"
          >
            Back to Apps
          </button>
          <button
            onClick={() => router.push("/workflow")}
            className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900 transition"
          >
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Verify</h1>
          <p className="mt-2 text-slate-300">
            Verification Intelligence: TB + SVA + Coverage plan + Simulation summary (optional formal/golden model).
          </p>
          {pwmChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              PWM full-stack demo: verify the generated controller RTL before creating Rust firmware that drives it.
            </div>
          ) : uartChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              UART packet-engine demo: verify FIFO levels, packet movement, interrupt status, and error handling before firmware generation.
            </div>
          ) : imageChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Image DMA demo: verify DMA progress, register-based line buffers, filter modes, histogram updates, and frame-done interrupt behavior.
            </div>
          ) : sensorChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Smart sensor hub demo: verify periodic sampling, FIFO telemetry, threshold alerts, IRQ clear, and low-power behavior before firmware generation.
            </div>
          ) : secureChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Secure boot demo: verify image authentication, rollback failure, tamper handling, debug lock, audit count, and security IRQ behavior.
            </div>
          ) : safetyChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Safety fault demo: verify watchdog heartbeat, timeout, fault masks, escalation, reset request, and safety IRQ behavior.
            </div>
          ) : null}

          {pwmChainDemo || uartChainDemo || imageChainDemo || sensorChainDemo || secureChainDemo || safetyChainDemo || handoffFlow ? (
            <div className="mt-4 flex flex-wrap items-center gap-2 text-xs">
              {["RTL", "Verify", "Firmware", "Software", "Validation", "Product"].map((stage, index, stages) => (
                <div key={stage} className="flex items-center gap-2">
                  <span
                    className={`rounded-full border px-3 py-1 font-semibold ${
                      stage === "Verify"
                        ? "border-cyan-400 bg-cyan-500 text-black"
                        : "border-slate-700 bg-black/30 text-slate-300"
                    }`}
                  >
                    {stage}
                  </span>
                  {index < stages.length - 1 ? <span className="text-slate-600">&gt;</span> : null}
                </div>
              ))}
            </div>
          ) : null}

          <div className="mt-6 grid gap-5 lg:grid-cols-[minmax(0,0.95fr)_minmax(420px,0.85fr)]">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">RTL source</label>
              <select
                value={rtlSourceMode}
                onChange={(e) => setRtlSourceMode(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="repo_path">Repo / path</option>
                <option value="from_arch2rtl">Use Arch2RTL output</option>
                <option value="paste">Paste RTL</option>
              </select>

              {rtlSourceMode === "repo_path" ? (
                <>
                  <label className="block text-sm text-slate-300">Repo path *</label>
                  <input
                    value={repoPath}
                    onChange={(e) => setRepoPath(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="/path/to/repo or git URL"
                  />
                </>
              ) : null}

              {rtlSourceMode === "from_arch2rtl" ? (
                <>
                  <label className="block text-sm text-slate-300">From workflow_id *</label>
                  <input
                    value={fromWorkflowId}
                    onChange={(e) => setFromWorkflowId(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="workflow_id from Arch2RTL"
                  />
                </>
              ) : null}

              <VoiceSpecDraft
                title="Verification Voice Spec"
                loopType="validation"
                target="Verification test intent"
                compact
                onApply={setTestIntent}
              />

              <label className="block text-sm text-slate-300">Test intent *</label>
              <textarea
                value={testIntent}
                onChange={(e) => setTestIntent(e.target.value)}
                rows={6}
                className="w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="What should the testbench verify? Any scenarios, reset behavior, corner cases…"
              />

              <div className="grid grid-cols-2 gap-3">
                <div>
                  <label className="block text-sm text-slate-300">Test mix</label>
                  <select
                    value={randomVsDirected}
                    onChange={(e) => setRandomVsDirected(e.target.value as any)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="both">Directed then random</option>
                    <option value="directed">Directed only</option>
                    <option value="random">Random only</option>
                  </select>
                </div>

                <div>
                  <label className="block text-sm text-slate-300">Seeds per testcase</label>
                  <input
                    type="number"
                    min={1}
                    value={seedCount}
                    onChange={(e) => setSeedCount(parseInt(e.target.value || "10", 10))}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  />
                </div>
              </div>

              <label className="block text-sm text-slate-300">Coverage targets (optional)</label>
              <input
                value={coverageTargets}
                onChange={(e) => setCoverageTargets(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="e.g., 90% line, 80% functional"
              />
              <div className="text-xs text-slate-500">
                Reported coverage is functional bin coverage generated from the RTL specification.
              </div>

              <div className="grid grid-cols-2 gap-3">
                <div>
                  <label className="block text-sm text-slate-300">Simulator tool</label>
                  <select
                    value={simulatorType}
                    onChange={(e) => setSimulatorType(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="verilator">Verilator + Cocotb</option>
                    <option value="icarus" disabled>Icarus Verilog (planned)</option>
                    <option value="questa" disabled>Questa (planned)</option>
                    <option value="vcs" disabled>VCS (planned)</option>
                    <option value="xcelium" disabled>Xcelium (planned)</option>
                  </select>
                </div>
                <div>
                  <label className="block text-sm text-slate-300">Code coverage tool</label>
                  <select
                    value={codeCoverageTool}
                    onChange={(e) => setCodeCoverageTool(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="verilator_coverage">verilator_coverage</option>
                    <option value="none">Disabled</option>
                    <option value="urg" disabled>Synopsys URG (planned)</option>
                    <option value="imc" disabled>Cadence IMC (planned)</option>
                    <option value="vcover" disabled>Questa vcover (planned)</option>
                  </select>
                </div>
                <div>
                  <label className="block text-sm text-slate-300">Formal tool</label>
                  <select
                    value={formalTool}
                    onChange={(e) => setFormalTool(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="none">Disabled</option>
                    <option value="symbiyosys">SymbiYosys (sby)</option>
                    <option value="jasper" disabled>JasperGold (planned)</option>
                    <option value="vc_formal" disabled>VC Formal (planned)</option>
                  </select>
                </div>
                <div>
                  <label className="block text-sm text-slate-300">Formal solver</label>
                  <select
                    value={formalSolver}
                    onChange={(e) => setFormalSolver(e.target.value)}
                    disabled={formalTool === "none"}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100 disabled:opacity-60"
                  >
                    <option value="z3">Z3</option>
                    <option value="boolector">Boolector</option>
                  </select>
                </div>
                <div className="col-span-2">
                  <label className="block text-sm text-slate-300">Golden model comparison</label>
                  <select
                    value={goldenModelTool}
                    onChange={(e) => setGoldenModelTool(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="none">Disabled</option>
                    <option value="chiploop_python_scoreboard">ChipLoop Python scoreboard</option>
                    <option value="custom_python" disabled>Custom Python model (planned)</option>
                    <option value="matlab" disabled>MATLAB reference model (planned)</option>
                  </select>
                </div>
              </div>

              <div className="rounded-xl border border-slate-800 bg-black/20 p-3 text-xs text-slate-400">
                Active tools: {simulatorType || "verilator"} simulation, {codeCoverageTool === "none" ? "no code coverage" : codeCoverageTool}, {formalTool === "none" ? "formal disabled" : `${formalTool} + ${formalSolver}`}, {goldenModelTool === "none" ? "golden model disabled" : goldenModelTool}.
              </div>

              <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                <input
                  type="checkbox"
                  checked={runClosureAnalysis}
                  onChange={(e) => setRunClosureAnalysis(e.target.checked)}
                  className="mt-1"
                />
                <span>
                  Run closure analysis after Verify
                  <span className="mt-1 block text-xs text-slate-500">
                    Starts a linked child workflow when Verify completes to analyze coverage gaps, failing seeds, and recommended next actions.
                  </span>
                </span>
              </label>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run Verify"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}
            </div>

            <div className="space-y-4">
              {rtlSourceMode === "paste" ? (
                <div>
              <label className="block text-sm text-slate-300">Paste RTL (only if RTL source = paste)</label>
              <textarea
                value={pastedRtl}
                onChange={(e) => setPastedRtl(e.target.value)}
                rows={rtlSourceMode === "paste" ? 18 : 8}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste your RTL here… (minimal mode stores it as rtl/top.sv)"
                disabled={rtlSourceMode !== "paste"}
              />
              <div className="mt-2 text-xs text-slate-500">
                Minimal mode: saved as one file. We can enhance later to multi-file paste.
              </div>
                </div>
              ) : null}
              {rtlSourceMode !== "paste" ? (
                <div className="rounded-2xl border border-slate-800 bg-black/20 p-4 text-sm text-slate-300">
                  <div className="font-semibold text-slate-100">RTL source</div>
                  {rtlSourceMode === "from_arch2rtl" ? (
                    <div className="mt-2">
                      Imported from Arch2RTL workflow:{" "}
                      <span className="break-all text-slate-100">{fromWorkflowId || "not selected"}</span>
                    </div>
                  ) : (
                    <div className="mt-2">
                      Repo / path: <span className="break-all text-slate-100">{repoPath || "not selected"}</span>
                    </div>
                  )}
                </div>
              ) : null}

              {workflowId ? (
                <>
                  <div className="rounded-2xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                    <div className="font-semibold text-slate-100">Run Status</div>
                    {rtlSourceMode === "from_arch2rtl" ? (
                      <div className="mt-2">
                        source Arch2RTL workflow_id:{" "}
                        <span className="break-all text-slate-100">{fromWorkflowId || "not selected"}</span>
                      </div>
                    ) : null}
                    <div className="mt-1">
                      Verify workflow_id: <span className="break-all text-slate-100">{workflowId}</span>
                    </div>
                    <div className="mt-1">
                      run_id: <span className="break-all text-slate-100">{runId}</span>
                    </div>
                    <div className="mt-1">
                      status: <span className="text-slate-100">{workflowRow?.status || "queued"}</span>
                    </div>
                    <div className="mt-3 flex flex-wrap gap-2">
                      <button
                        onClick={downloadZip}
                        className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
                      >
                        Download ZIP (full=1)
                      </button>
                      <button
                        onClick={analyzeClosure}
                        disabled={workflowRow?.status !== "completed" || Boolean(closureWorkflowId)}
                        className="rounded-xl bg-cyan-700 px-4 py-2 font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
                      >
                        Analyze Closure Gaps
                      </button>
                      {handoffFlow && rtlSourceMode === "from_arch2rtl" ? (
                        <button
                          onClick={openInEmbeddedFirmware}
                          disabled={workflowRow?.status !== "completed"}
                          className="rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                        >
                          Open in Firmware
                        </button>
                      ) : null}
                    </div>
                    {rtlSourceMode === "from_arch2rtl" ? (
                      <div className="mt-3">
                        <NextWorkflowLauncher
                          currentStage="verify"
                          currentWorkflowId={workflowId}
                          currentRunId={runId}
                          sourceArch2RTLWorkflowId={fromWorkflowId}
                          upstreamWorkflows={{ ...upstreamWorkflows, arch2rtl: fromWorkflowId, verify: workflowId }}
                          disabled={workflowRow?.status !== "completed"}
                        />
                      </div>
                    ) : null}
                  </div>

                  <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="verification" logs={workflowRow?.logs} />

                  {closureWorkflowId ? (
                    <div className="rounded-2xl border border-cyan-900/60 bg-cyan-950/15 p-4 text-sm text-slate-300">
                      <div className="font-semibold text-cyan-200">Verification Closure Analysis</div>
                      <div className="mt-2">
                        closure workflow_id: <span className="break-all text-slate-100">{closureWorkflowId}</span>
                      </div>
                      <div>
                        closure run_id: <span className="break-all text-slate-100">{closureRunId}</span>
                      </div>
                      <div>
                        status: <span className="text-slate-100">{closureRow?.status || "queued"}</span>
                      </div>
                      <button
                        onClick={downloadClosureZip}
                        disabled={closureRow?.status !== "completed"}
                        className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 disabled:cursor-not-allowed disabled:bg-slate-700"
                      >
                        Download Closure Plan
                      </button>
                      <div className="mt-3 max-h-52 overflow-auto rounded-lg border border-slate-800 bg-black/30 p-3 font-mono text-xs text-slate-400">
                        {parseLogLines(closureRow?.logs).map((line, index) => (
                          <div key={`${line}-${index}`}>{line}</div>
                        ))}
                      </div>
                    </div>
                  ) : null}
                </>
              ) : (
                <div className="rounded-2xl border border-slate-800 bg-black/20 p-5 text-sm text-slate-400">
                  Run evidence appears here after Verify completes.
                </div>
              )}
            </div>
          </div>

          {workflowId ? (
            <div className="mt-6">
              <AskThisRunPanel workflowId={workflowId} compact />
            </div>
          ) : null}

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div
              ref={logsRef}
              className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200"
            >
              {logLines.length ? (
                logLines.map((l, i) => (
                  <div key={i} className="whitespace-pre-wrap">
                    {l}
                  </div>
                ))
              ) : (
                <div className="text-slate-500">No logs yet. Click “Run Verify”.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
