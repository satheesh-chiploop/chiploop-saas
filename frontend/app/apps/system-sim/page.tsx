"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TextFileUpload from "@/components/TextFileUpload";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import SpecTextBox from "@/components/SpecTextBox";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  SYSTEM_MIXED_SIGNAL_PREFILL_KEY,
  type DesignChainContext,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = { id: string; status?: string | null; phase?: string | null; logs?: string | null; updated_at?: string | null; };

function systemSimReady(row: WorkflowRow | null): boolean {
  if (!row) return false;
  const logs = row.logs || "";
  return row.status === "completed" || logs.includes("System App complete: System_Sim") || logs.includes("system_sim_coverage");
}

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
}

function mergeUploadedText(current: string, uploaded: string, mode: "append" | "replace") {
  if (mode === "append") return [current.trim(), uploaded.trim()].filter(Boolean).join("\n\n");
  return uploaded;
}

export default function SystemSimAppPage() {
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
  const [closureLoopWorkflowId, setClosureLoopWorkflowId] = useState<string | null>(null);
  const [closureLoopRunId, setClosureLoopRunId] = useState<string | null>(null);
  const [closureLoopRow, setClosureLoopRow] = useState<WorkflowRow | null>(null);

  const [projectName, setProjectName] = useState("");
  const [digitalSpecText, setDigitalSpecText] = useState("");
  const [analogSpecText, setAnalogSpecText] = useState("");
  const [socIntegrationSpecText, setSocIntegrationSpecText] = useState("");
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");
  const [testIntent, setTestIntent] = useState("");
  const [verificationPlan, setVerificationPlan] = useState("");
  const [monitorCheckerPlan, setMonitorCheckerPlan] = useState("");
  const [coverageTargets, setCoverageTargets] = useState("");
  const [coveragePlan, setCoveragePlan] = useState("");
  const [randomVsDirected, setRandomVsDirected] = useState<"random" | "directed" | "both">("both");
  const [simulatorType, setSimulatorType] = useState("verilator");
  const [codeCoverageTool, setCodeCoverageTool] = useState("verilator_coverage");
  const [runClosureAnalysis, setRunClosureAnalysis] = useState(false);
  const [runClosureLoopAfterVerify, setRunClosureLoopAfterVerify] = useState(false);
  const [debugFailuresAfterVerify, setDebugFailuresAfterVerify] = useState(false);
  const [failureDebugLogOnlyFirst, setFailureDebugLogOnlyFirst] = useState(true);
  const [failureDebugGenerateVcd, setFailureDebugGenerateVcd] = useState(true);
  const [failureDebugAutoApplyTb, setFailureDebugAutoApplyTb] = useState(false);
  const [failureDebugAutoApplyRtl, setFailureDebugAutoApplyRtl] = useState(false);
  const [failureDebugRerunFailing, setFailureDebugRerunFailing] = useState(true);
  const [closureMaxIterations, setClosureMaxIterations] = useState(1);
  const [closureSeedBudget, setClosureSeedBudget] = useState(10);
  const [closureRerunMode, setClosureRerunMode] = useState<"coverage_targeted" | "failed_only" | "full_regression">("coverage_targeted");
  const closureStartedRef = useRef(false);
  const closureLoopStartedRef = useRef(false);
  const [systemSimTestcases, setSystemSimTestcases] = useState("");
  const [systemSimSeeds, setSystemSimSeeds] = useState("");
  const [systemSimNumIters, setSystemSimNumIters] = useState(25);
  const [tempMonitorChain, setTempMonitorChain] = useState(false);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const readyForFirmware = useMemo(() => systemSimReady(workflowRow), [workflowRow]);
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

  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/system-sim");
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
    const isTempMonitor = params.get("tempmon_chain") === "1";
    setTempMonitorChain(isTempMonitor);
    try {
      const context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
      if (context.systemRtlWorkflowId) setSystemRtlWorkflowId(context.systemRtlWorkflowId);
    } catch {
      // ignore malformed handoff context
    }
    if (!isTempMonitor) return;
    const raw = window.localStorage.getItem(SYSTEM_MIXED_SIGNAL_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as {
        projectName?: string;
        digitalSpecText?: string;
        analogSpecText?: string;
        socIntegrationSpecText?: string;
        systemSimTestcases?: string;
        systemSimSeeds?: string;
        systemSimNumIters?: number;
      };
      setProjectName(prefill.projectName ? `${prefill.projectName}_sim` : "");
      setDigitalSpecText(prefill.digitalSpecText || "");
      setAnalogSpecText(prefill.analogSpecText || "");
      setSocIntegrationSpecText(prefill.socIntegrationSpecText || "");
      setSystemSimTestcases(prefill.systemSimTestcases || "reset_defaults, threshold_below, threshold_above, alert_clear");
      setTestIntent(prefill.systemSimTestcases || "Verify reset defaults, below-threshold behavior, above-threshold alert behavior, alert clear, and analog temperature macro observation points.");
      setSystemSimSeeds(prefill.systemSimSeeds || "1, 2, 7");
      setSystemSimNumIters(Number(prefill.systemSimNumIters || 40));
    } catch {
      window.localStorage.removeItem(SYSTEM_MIXED_SIGNAL_PREFILL_KEY);
    }
  }, [loading]);

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
      if (isActive && !error && data) setClosureRow(data as WorkflowRow);
    })();
    const channel = supabase.channel(`wf-${closureWorkflowId}`).on(
      "postgres_changes",
      { event: "*", schema: "public", table: "workflows", filter: `id=eq.${closureWorkflowId}` },
      (payload) => setClosureRow(payload.new as WorkflowRow),
    ).subscribe();
    return () => {
      isActive = false;
      supabase.removeChannel(channel);
    };
  }, [closureWorkflowId]);

  useEffect(() => {
    if (!closureLoopWorkflowId) return;
    let isActive = true;
    (async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", closureLoopWorkflowId)
        .single();
      if (isActive && !error && data) setClosureLoopRow(data as WorkflowRow);
    })();
    const channel = supabase.channel(`wf-${closureLoopWorkflowId}`).on(
      "postgres_changes",
      { event: "*", schema: "public", table: "workflows", filter: `id=eq.${closureLoopWorkflowId}` },
      (payload) => setClosureLoopRow(payload.new as WorkflowRow),
    ).subscribe();
    return () => {
      isActive = false;
      supabase.removeChannel(channel);
    };
  }, [closureLoopWorkflowId]);

  useEffect(() => {
    if (runClosureLoopAfterVerify || (!runClosureAnalysis && !debugFailuresAfterVerify) || closureStartedRef.current) return;
    if (!workflowId || workflowRow?.status !== "completed") return;
    closureStartedRef.current = true;
    void analyzeClosure();
  }, [runClosureAnalysis, runClosureLoopAfterVerify, debugFailuresAfterVerify, workflowId, workflowRow?.status]);

  useEffect(() => {
    if (!runClosureLoopAfterVerify || closureLoopStartedRef.current) return;
    if (!workflowId || workflowRow?.status !== "completed") return;
    closureLoopStartedRef.current = true;
    void runClosureLoop();
  }, [runClosureLoopAfterVerify, workflowId, workflowRow?.status]);

  const canRun = useMemo(() => {
    if (running) return false;
    if (!systemRtlWorkflowId.trim()) {
      if (!digitalSpecText.trim()) return false;
      if (!analogSpecText.trim()) return false;
      if (!socIntegrationSpecText.trim()) return false;
    }
    if (!testIntent.trim()) return false;
    return true;
  }, [running, systemRtlWorkflowId, digitalSpecText, analogSpecText, socIntegrationSpecText, testIntent]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    closureStartedRef.current = false;
    closureLoopStartedRef.current = false;
    setClosureWorkflowId(null);
    setClosureRunId(null);
    setClosureRow(null);
    setClosureLoopWorkflowId(null);
    setClosureLoopRunId(null);
    setClosureLoopRow(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/sim/run",
        {
          project_name: projectName || undefined,
          digital_spec_text: digitalSpecText,
          analog_spec_text: analogSpecText,
          soc_integration_spec_text: socIntegrationSpecText,
          system_rtl_workflow_id: systemRtlWorkflowId || undefined,
          test_intent: testIntent,
          verification_plan: verificationPlan || undefined,
          monitor_checker_plan: monitorCheckerPlan || undefined,
          coverage_targets: coverageTargets || undefined,
          coverage_plan: coveragePlan || undefined,
          random_vs_directed: randomVsDirected,
          simulator_type: simulatorType,
          seed_count: systemSimSeeds.split(",").filter((x) => x.trim()).length || undefined,
          system_sim_testcases: systemSimTestcases.split(",").map((x) => x.trim()).filter(Boolean),
          system_sim_seeds: systemSimSeeds.split(",").map((x) => Number(x.trim())).filter((x) => Number.isFinite(x)),
          system_sim_num_iters: systemSimNumIters,
          toolchain: {
            simulator: simulatorType,
            code_coverage: codeCoverageTool,
          },
          run_closure_analysis: runClosureLoopAfterVerify || runClosureAnalysis || debugFailuresAfterVerify,
          enable_failure_debug: debugFailuresAfterVerify,
          failure_debug_options: {
            enabled: debugFailuresAfterVerify,
            log_only_first: failureDebugLogOnlyFirst,
            generate_vcd_if_inconclusive: failureDebugGenerateVcd,
            auto_apply_testbench_fixes: failureDebugAutoApplyTb,
            auto_apply_rtl_fixes: failureDebugAutoApplyRtl,
            rerun_failing_tests: failureDebugRerunFailing,
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

  function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
  }

  async function analyzeClosure() {
    if (!workflowId) return;
    setErr(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/verify/closure/run", {
        source_verify_workflow_id: workflowId,
        coverage_targets: coverageTargets || undefined,
        seed_count: systemSimSeeds.split(",").filter((x) => x.trim()).length || 5,
        toolchain: { simulator: simulatorType, code_coverage: codeCoverageTool },
        enable_failure_debug: debugFailuresAfterVerify,
        failure_debug_options: {
          enabled: debugFailuresAfterVerify,
          log_only_first: failureDebugLogOnlyFirst,
          generate_vcd_if_inconclusive: failureDebugGenerateVcd,
          auto_apply_testbench_fixes: failureDebugAutoApplyTb,
          auto_apply_rtl_fixes: failureDebugAutoApplyRtl,
          rerun_failing_tests: failureDebugRerunFailing,
        },
      });
      setClosureWorkflowId(out.workflow_id);
      setClosureRunId(out.run_id);
    } catch (e: any) {
      closureStartedRef.current = false;
      setErr(e?.message || String(e));
    }
  }

  async function runClosureLoop() {
    if (!workflowId) return;
    setErr(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/verify/closure-loop/run", {
        source_verify_workflow_id: workflowId,
        coverage_targets: coverageTargets || undefined,
        seed_count: systemSimSeeds.split(",").filter((x) => x.trim()).length || 5,
        seed_budget: closureSeedBudget,
        max_iterations: closureMaxIterations,
        rerun_mode: closureRerunMode,
        random_vs_directed: randomVsDirected,
        toolchain: { simulator: simulatorType, code_coverage: codeCoverageTool },
        enable_failure_debug: debugFailuresAfterVerify,
        failure_debug_options: {
          enabled: debugFailuresAfterVerify,
          log_only_first: failureDebugLogOnlyFirst,
          generate_vcd_if_inconclusive: failureDebugGenerateVcd,
          auto_apply_testbench_fixes: failureDebugAutoApplyTb,
          auto_apply_rtl_fixes: failureDebugAutoApplyRtl,
          rerun_failing_tests: failureDebugRerunFailing,
        },
      });
      setClosureLoopWorkflowId(out.workflow_id);
      setClosureLoopRunId(out.run_id);
    } catch (e: any) {
      closureLoopStartedRef.current = false;
      setErr(e?.message || String(e));
    }
  }

  function downloadClosureZip() {
    if (!closureWorkflowId) return;
    window.open(`${API_BASE}/workflow/${closureWorkflowId}/download_zip?full=1`, "_blank");
  }

  function downloadClosureLoopZip() {
    if (!closureLoopWorkflowId) return;
    window.open(`${API_BASE}/workflow/${closureLoopWorkflowId}/download_zip?full=1`, "_blank");
  }

  function openSystemFirmware() {
    if (!workflowId) return;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.demoKind = tempMonitorChain ? "temp_monitor_system" : context.demoKind;
    if (systemRtlWorkflowId.trim()) context.systemRtlWorkflowId = systemRtlWorkflowId.trim();
    context.systemSimWorkflowId = workflowId;
    context.systemSimRunId = runId || undefined;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    router.push(`/apps/system-firmware${tempMonitorChain ? "?tempmon_chain=1" : ""}`);
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
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">System Sim</h1>
          {tempMonitorChain ? (
            <div className="mt-4 rounded-xl border border-emerald-800/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Temperature Monitor System journey: run System Sim with configurable testcases, seeds, iteration budget, and coverage evidence before firmware handoff.
            </div>
          ) : null}
          <p className="mt-2 text-slate-300">SoC integration + simulation + coverage + waveforms → ZIP.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input
                value={projectName}
                onChange={(e) => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              />
              <label className="block text-sm text-slate-300">Start from System RTL workflow ID</label>
              <input
                value={systemRtlWorkflowId}
                onChange={(e) => setSystemRtlWorkflowId(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="Optional: skip System RTL generation and verify this source workflow"
              />
              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-200">System Sim run settings</div>
                <label className="mt-3 block text-sm text-slate-300">Test intent *</label>
                <textarea
                  value={testIntent}
                  onChange={(e) => setTestIntent(e.target.value)}
                  rows={4}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Scenarios, expected behavior, corner cases, analog macro observations, and pass/fail intent..."
                />
                <TextFileUpload
                  compact
                  label="Upload verification spec or test intent"
                  helper="Load a test intent, verification note, markdown plan, or structured JSON/YAML."
                  onText={(text, _fileName, mode) => setTestIntent((current) => mergeUploadedText(current, text, mode))}
                />
                <label className="mt-3 block text-sm text-slate-300">Testcases</label>
                <input
                  value={systemSimTestcases}
                  onChange={(e) => setSystemSimTestcases(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="reset_defaults, threshold_below, threshold_above"
                />
                <label className="mt-3 block text-sm text-slate-300">Seeds</label>
                <input
                  value={systemSimSeeds}
                  onChange={(e) => setSystemSimSeeds(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="1, 2, 7"
                />
                <label className="mt-3 block text-sm text-slate-300">Iteration budget</label>
                <input
                  type="number"
                  min={1}
                  value={systemSimNumIters}
                  onChange={(e) => setSystemSimNumIters(Number(e.target.value || 1))}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                />
                <label className="mt-3 block text-sm text-slate-300">Coverage targets</label>
                <input
                  value={coverageTargets}
                  onChange={(e) => setCoverageTargets(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="Example: functional 85%, line 80%, branch 70%"
                />
                <TextFileUpload
                  compact
                  label="Upload coverage point plan"
                  helper="Coverpoints, bins, exclusions, analog macro observation points, and closure goals."
                  onText={(text, _fileName, mode) => setCoveragePlan((current) => mergeUploadedText(current, text, mode))}
                />
                <textarea
                  value={coveragePlan}
                  onChange={(e) => setCoveragePlan(e.target.value)}
                  rows={4}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Functional/code coverage points, bins, crosses, exclusions..."
                />
                <TextFileUpload
                  compact
                  label="Upload verification plan"
                  helper="Reviewer-authored verification plan kept with run evidence."
                  onText={(text, _fileName, mode) => setVerificationPlan((current) => mergeUploadedText(current, text, mode))}
                />
                <textarea
                  value={verificationPlan}
                  onChange={(e) => setVerificationPlan(e.target.value)}
                  rows={3}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Verification objectives, scenarios, assumptions, scoreboarding, assertions, and exclusions..."
                />
                <TextFileUpload
                  compact
                  label="Upload monitor/checker plan"
                  helper="Monitor points, scoreboard/checker rules, protocol checks, analog macro sampled observations."
                  onText={(text, _fileName, mode) => setMonitorCheckerPlan((current) => mergeUploadedText(current, text, mode))}
                />
                <textarea
                  value={monitorCheckerPlan}
                  onChange={(e) => setMonitorCheckerPlan(e.target.value)}
                  rows={3}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="What should monitors observe and what should scoreboards/checkers compare?"
                />
                <div className="mt-3 grid gap-3 sm:grid-cols-3">
                  <label className="block text-sm text-slate-300">
                    Test style
                    <select value={randomVsDirected} onChange={(e) => setRandomVsDirected(e.target.value as "random" | "directed" | "both")} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="both">Directed + random</option>
                      <option value="directed">Directed only</option>
                      <option value="random">Random only</option>
                    </select>
                  </label>
                  <label className="block text-sm text-slate-300">
                    Simulator
                    <select value={simulatorType} onChange={(e) => setSimulatorType(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="verilator">verilator</option>
                      <option value="icarus">icarus</option>
                    </select>
                  </label>
                  <label className="block text-sm text-slate-300">
                    Code coverage
                    <select value={codeCoverageTool} onChange={(e) => setCodeCoverageTool(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="verilator_coverage">verilator_coverage</option>
                      <option value="none">none</option>
                    </select>
                  </label>
                </div>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runClosureLoopAfterVerify || runClosureAnalysis} onChange={(e) => setRunClosureAnalysis(e.target.checked)} disabled={runClosureLoopAfterVerify} className="mt-1" />
                  <span>Run closure analysis after System Sim</span>
                </label>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runClosureLoopAfterVerify} onChange={(e) => setRunClosureLoopAfterVerify(e.target.checked)} className="mt-1" />
                  <span>Run closure loop after System Sim</span>
                </label>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={debugFailuresAfterVerify} onChange={(e) => setDebugFailuresAfterVerify(e.target.checked)} className="mt-1" />
                  <span>Debug failing tests after System Sim</span>
                </label>
                {debugFailuresAfterVerify ? (
                  <div className="mt-3 rounded-xl border border-slate-800 bg-black/20 p-3">
                    <div className="text-sm font-semibold text-slate-100">Failure debug settings</div>
                    <div className="mt-1 text-xs text-slate-500">
                      RTL and testbench fixes are proposal-only unless auto-apply is explicitly enabled.
                    </div>
                    <div className="mt-3 grid grid-cols-2 gap-3 text-xs text-slate-300">
                      <label className="flex items-center gap-2">
                        <input type="checkbox" checked={failureDebugLogOnlyFirst} onChange={(e) => setFailureDebugLogOnlyFirst(e.target.checked)} />
                        Log-only debug first
                      </label>
                      <label className="flex items-center gap-2">
                        <input type="checkbox" checked={failureDebugGenerateVcd} onChange={(e) => setFailureDebugGenerateVcd(e.target.checked)} />
                        Generate VCD if inconclusive
                      </label>
                      <label className="flex items-center gap-2">
                        <input type="checkbox" checked={failureDebugRerunFailing} onChange={(e) => setFailureDebugRerunFailing(e.target.checked)} />
                        Rerun failing tests
                      </label>
                      <label className="flex items-center gap-2">
                        <input type="checkbox" checked={failureDebugAutoApplyTb} onChange={(e) => setFailureDebugAutoApplyTb(e.target.checked)} />
                        Auto-apply testbench fixes
                      </label>
                      <label className="col-span-2 flex items-center gap-2 text-amber-200">
                        <input type="checkbox" checked={failureDebugAutoApplyRtl} onChange={(e) => setFailureDebugAutoApplyRtl(e.target.checked)} />
                        Auto-apply RTL fixes
                      </label>
                    </div>
                  </div>
                ) : null}
                {runClosureLoopAfterVerify ? (
                  <div className="mt-3 grid grid-cols-3 gap-3">
                    <input type="number" min={1} max={10} value={closureMaxIterations} onChange={(e) => setClosureMaxIterations(Number(e.target.value || 1))} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" title="Iterations" />
                    <input type="number" min={1} max={100} value={closureSeedBudget} onChange={(e) => setClosureSeedBudget(Number(e.target.value || 10))} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" title="Seed budget" />
                    <select value={closureRerunMode} onChange={(e) => setClosureRerunMode(e.target.value as any)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="coverage_targeted">Coverage targeted</option>
                      <option value="failed_only">Failed only</option>
                      <option value="full_regression">Full regression</option>
                    </select>
                  </div>
                ) : null}
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-amber-600 hover:bg-amber-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System Sim"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

              {workflowId ? (
                <div className="mt-4 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>workflow_id: <span className="text-slate-100">{workflowId}</span></div>
                  <div>run_id: <span className="text-slate-100">{runId}</span></div>
                  <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                    Download ZIP (full=1)
                  </button>
                  <button
                    type="button"
                    onClick={openSystemFirmware}
                    disabled={!readyForFirmware}
                    className="ml-3 mt-3 rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Open System Firmware
                  </button>
                  <button
                    type="button"
                    onClick={analyzeClosure}
                    disabled={workflowRow?.status !== "completed" || Boolean(closureWorkflowId)}
                    className="ml-3 mt-3 rounded-xl bg-cyan-700 px-4 py-2 font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Analyze Closure
                  </button>
                  <button
                    type="button"
                    onClick={runClosureLoop}
                    disabled={workflowRow?.status !== "completed" || Boolean(closureLoopWorkflowId)}
                    className="ml-3 mt-3 rounded-xl bg-violet-700 px-4 py-2 font-semibold text-white hover:bg-violet-600 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Run Closure Loop
                  </button>
                  <div className="mt-4">
                    <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="verification" logs={workflowRow?.logs} />
                  </div>
                  {closureWorkflowId ? (
                    <div className="mt-4 rounded-xl border border-cyan-900/60 bg-cyan-950/15 p-3">
                      <div className="font-semibold text-cyan-200">System Sim Closure Analysis</div>
                      <div>workflow_id: <span className="break-all text-slate-100">{closureWorkflowId}</span></div>
                      <div>run_id: <span className="break-all text-slate-100">{closureRunId}</span></div>
                      <div>status: <span className="text-slate-100">{closureRow?.status || "queued"}</span></div>
                      <button onClick={downloadClosureZip} disabled={closureRow?.status !== "completed"} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 disabled:cursor-not-allowed disabled:bg-slate-700">
                        Download Closure Plan
                      </button>
                    </div>
                  ) : null}
                  {closureLoopWorkflowId ? (
                    <div className="mt-4 rounded-xl border border-violet-900/60 bg-violet-950/15 p-3">
                      <div className="font-semibold text-violet-200">System Sim Closure Loop</div>
                      <div>workflow_id: <span className="break-all text-slate-100">{closureLoopWorkflowId}</span></div>
                      <div>run_id: <span className="break-all text-slate-100">{closureLoopRunId}</span></div>
                      <div>status: <span className="text-slate-100">{closureLoopRow?.status || "queued"}</span></div>
                      <button onClick={downloadClosureLoopZip} disabled={closureLoopRow?.status !== "completed"} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 disabled:cursor-not-allowed disabled:bg-slate-700">
                        Download Closure Loop
                      </button>
                    </div>
                  ) : null}
                  <AskThisRunPanel workflowId={workflowId} compact />
                </div>
              ) : null}
            </div>

            <div className="space-y-4">
              <SpecTextBox
                label="Digital specification"
                required
                value={digitalSpecText}
                onChange={setDigitalSpecText}
                voiceTitle="Digital Voice Spec"
                voiceLoopType="digital"
                voiceTarget="System digital spec"
                uploadLabel="Upload digital spec"
                uploadHelper="Digital behavior, interfaces, registers, and verification-relevant requirements."
              />
              <SpecTextBox
                label="Analog specification"
                required
                value={analogSpecText}
                onChange={setAnalogSpecText}
                voiceTitle="Analog Voice Spec"
                voiceLoopType="analog"
                voiceTarget="System analog spec"
                uploadLabel="Upload analog macro spec"
                uploadHelper="Analog macro model/pins/observability; System Sim treats analog as a macro abstraction."
              />
              <SpecTextBox
                label="SoC integration specification"
                required
                value={socIntegrationSpecText}
                onChange={setSocIntegrationSpecText}
                voiceTitle="SoC Voice Spec"
                voiceLoopType="system"
                voiceTarget="SoC integration spec"
                uploadLabel="Upload SoC integration spec"
                uploadHelper="Top-level integration, macro hookups, clock/reset/power assumptions, and system scenarios."
              />
            </div>
          </div>

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((l, i) => <div key={i} className="whitespace-pre-wrap">{l}</div>) : (
                <div className="text-slate-500">No logs yet. Click “Run System Sim”.</div>
              )}
            </div>
          </div>

        </div>
      </div>
    </main>
  );
}
