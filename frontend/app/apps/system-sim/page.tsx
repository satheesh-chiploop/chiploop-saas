"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import {
  HemAutomaticRunControls,
  HemChildDashboardLinks,
  SYSTEM_HEM_DEFAULT_STAGE_TOGGLES,
  SYSTEM_HEM_GOAL_OPTIONS,
  type SystemHemGoal,
  systemHemStageOptions,
} from "@/components/HemAutomaticRun";
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
type SystemRtlSourceMode = "from_system_rtl" | "paste" | "repo_path";

function systemSimReady(row: WorkflowRow | null): boolean {
  if (!row) return false;
  const logs = row.logs || "";
  return row.status === "completed" || logs.includes("System App complete: System_Sim") || logs.includes("system_sim_coverage");
}

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
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
  const [closureChart, setClosureChart] = useState<any | null>(null);

  const [projectName, setProjectName] = useState("");
  const [rtlSourceMode, setRtlSourceMode] = useState<SystemRtlSourceMode>("from_system_rtl");
  const [repoPath, setRepoPath] = useState("");
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
  const [formalTool, setFormalTool] = useState("none");
  const [formalSolver, setFormalSolver] = useState("z3");
  const [goldenModelTool, setGoldenModelTool] = useState("none");
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
  const [hemEnabled, setHemEnabled] = useState(false);
  const [hemAdaptive, setHemAdaptive] = useState(false);
  const [hemGoal, setHemGoal] = useState<SystemHemGoal>("product_demo");
  const [hemStageToggles, setHemStageToggles] = useState({ ...SYSTEM_HEM_DEFAULT_STAGE_TOGGLES });

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

  async function getJSON<T>(path: string): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, { headers: authHeaders() });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` - ${txt}` : ""}`);
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
      if (context.systemRtlWorkflowId) {
        setSystemRtlWorkflowId(context.systemRtlWorkflowId);
        setRtlSourceMode("from_system_rtl");
      }
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
    if (!closureLoopWorkflowId || closureLoopRow?.status !== "completed") return;
    (async () => {
      try {
        const data = await getJSON<any>(`/apps/dashboard/artifact/${closureLoopWorkflowId}?filename=closure_chart.json`);
        setClosureChart(data);
      } catch {
        setClosureChart(null);
      }
    })();
  }, [closureLoopWorkflowId, closureLoopRow?.status]);

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
    if (rtlSourceMode === "from_system_rtl" && !systemRtlWorkflowId.trim()) return false;
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "paste" && ![digitalSpecText, analogSpecText, socIntegrationSpecText].some((text) => text.trim())) return false;
    if (!testIntent.trim()) return false;
    return true;
  }, [running, rtlSourceMode, systemRtlWorkflowId, repoPath, digitalSpecText, analogSpecText, socIntegrationSpecText, testIntent]);

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
    setClosureChart(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/sim/run",
        {
          project_name: projectName || undefined,
          rtl_source_mode: rtlSourceMode,
          digital_spec_text: rtlSourceMode === "paste" ? "" : digitalSpecText,
          analog_spec_text: rtlSourceMode === "paste" ? "" : analogSpecText,
          soc_integration_spec_text: rtlSourceMode === "paste" ? "" : socIntegrationSpecText,
          system_rtl_workflow_id: rtlSourceMode === "from_system_rtl" ? systemRtlWorkflowId : undefined,
          from_workflow_id: rtlSourceMode === "from_system_rtl" ? systemRtlWorkflowId : undefined,
          repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
          pasted_rtl_files:
            rtlSourceMode === "paste"
              ? [
                  { path: "rtl/system_digital.sv", content: digitalSpecText },
                  { path: "rtl/system_analog_model.sv", content: analogSpecText },
                  { path: "rtl/system_soc.sv", content: socIntegrationSpecText },
                ].filter((item) => item.content.trim())
              : undefined,
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
            formal: formalTool,
            formal_solver: formalSolver,
            golden_model: goldenModelTool,
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
          toggles: {
            enable_formal: formalTool !== "none",
            enable_golden_model: goldenModelTool !== "none",
          },
          hem_enabled: hemEnabled,
          hem_mode: hemAdaptive ? "adaptive" : "fixed",
          hem_goal: hemGoal,
          hem_stage_toggles: hemStageToggles,
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
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/system/sim/closure/run", {
        source_verify_workflow_id: workflowId,
        coverage_targets: coverageTargets || undefined,
        seed_count: systemSimSeeds.split(",").filter((x) => x.trim()).length || 5,
        toolchain: { simulator: simulatorType, code_coverage: codeCoverageTool, formal: formalTool, formal_solver: formalSolver, golden_model: goldenModelTool },
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
    setClosureChart(null);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/system/sim/closure-loop/run", {
        source_verify_workflow_id: workflowId,
        coverage_targets: coverageTargets || undefined,
        seed_count: systemSimSeeds.split(",").filter((x) => x.trim()).length || 5,
        seed_budget: closureSeedBudget,
        max_iterations: closureMaxIterations,
        rerun_mode: closureRerunMode,
        random_vs_directed: randomVsDirected,
        toolchain: { simulator: simulatorType, code_coverage: codeCoverageTool, formal: formalTool, formal_solver: formalSolver, golden_model: goldenModelTool },
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
      <div className="mx-auto max-w-[1440px] px-6 py-10">
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
              <label className="block text-sm text-slate-300">RTL source</label>
              <select
                value={rtlSourceMode}
                onChange={(e) => setRtlSourceMode(e.target.value as SystemRtlSourceMode)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="from_system_rtl">Use System RTL output</option>
                <option value="repo_path">Repo / path</option>
                <option value="paste">Paste RTL</option>
              </select>
              {rtlSourceMode === "from_system_rtl" ? (
                <>
                  <label className="block text-sm text-slate-300">System RTL workflow_id *</label>
                  <input
                    value={systemRtlWorkflowId}
                    onChange={(e) => setSystemRtlWorkflowId(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="workflow_id from System RTL"
                  />
                </>
              ) : null}
              {rtlSourceMode === "repo_path" ? (
                <>
                  <label className="block text-sm text-slate-300">Repo/path *</label>
                  <input
                    value={repoPath}
                    onChange={(e) => setRepoPath(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="/path/to/repo or checked-out RTL directory"
                  />
                </>
              ) : null}
              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-200">System Sim run settings</div>
                <SpecTextBox
                  label="Test intent"
                  required
                  value={testIntent}
                  onChange={setTestIntent}
                  rows={4}
                  voiceTitle="System Sim Voice Spec"
                  voiceLoopType="validation"
                  voiceTarget="System simulation test intent"
                  uploadLabel="Upload verification spec or test intent"
                  uploadHelper="Load a test intent, verification note, markdown plan, or structured JSON/YAML."
                  placeholder="Scenarios, expected behavior, corner cases, analog macro observations, and pass/fail intent..."
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
                <SpecTextBox
                  label="Coverage point plan"
                  value={coveragePlan}
                  onChange={setCoveragePlan}
                  rows={4}
                  voiceTitle="Coverage Plan Voice Spec"
                  voiceLoopType="validation"
                  voiceTarget="System simulation coverage point plan"
                  uploadLabel="Upload coverage point plan"
                  uploadHelper="Coverpoints, bins, exclusions, analog macro observation points, and closure goals."
                  placeholder="Functional/code coverage points, bins, crosses, exclusions..."
                />
                <SpecTextBox
                  label="Verification plan"
                  value={verificationPlan}
                  onChange={setVerificationPlan}
                  rows={3}
                  voiceTitle="Verification Plan Voice Spec"
                  voiceLoopType="validation"
                  voiceTarget="System simulation verification plan"
                  uploadLabel="Upload verification plan"
                  uploadHelper="Reviewer-authored verification plan kept with run evidence."
                  placeholder="Verification objectives, scenarios, assumptions, scoreboarding, assertions, and exclusions..."
                />
                <SpecTextBox
                  label="Monitor/checker plan"
                  value={monitorCheckerPlan}
                  onChange={setMonitorCheckerPlan}
                  rows={3}
                  voiceTitle="Monitor/Checker Voice Spec"
                  voiceLoopType="validation"
                  voiceTarget="System simulation monitor/checker plan"
                  uploadLabel="Upload monitor/checker plan"
                  uploadHelper="Monitor points, scoreboard/checker rules, protocol checks, analog macro sampled observations."
                  placeholder="What should monitors observe and what should scoreboards/checkers compare?"
                />
                <div className="mt-3 grid gap-3 sm:grid-cols-2">
                  <label className="block text-sm text-slate-300">
                    Test mix
                    <select value={randomVsDirected} onChange={(e) => setRandomVsDirected(e.target.value as "random" | "directed" | "both")} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="both">Directed then random</option>
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
                      <option value="none">Disabled</option>
                    </select>
                  </label>
                  <label className="block text-sm text-slate-300">
                    Formal tool
                    <select value={formalTool} onChange={(e) => setFormalTool(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="none">Disabled</option>
                      <option value="symbiyosys">SymbiYosys (sby)</option>
                    </select>
                  </label>
                  <label className="block text-sm text-slate-300">
                    Formal solver
                    <select value={formalSolver} onChange={(e) => setFormalSolver(e.target.value)} disabled={formalTool === "none"} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100 disabled:opacity-60">
                      <option value="z3">Z3</option>
                      <option value="boolector">Boolector</option>
                    </select>
                  </label>
                  <label className="block text-sm text-slate-300 sm:col-span-2">
                    Golden model comparison
                    <select value={goldenModelTool} onChange={(e) => setGoldenModelTool(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                      <option value="none">Disabled</option>
                      <option value="chiploop_python_scoreboard">ChipLoop Python scoreboard</option>
                    </select>
                  </label>
                </div>
                <div className="mt-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-xs text-slate-400">
                  Active tools: {simulatorType || "verilator"} simulation, {codeCoverageTool === "none" ? "no code coverage" : codeCoverageTool}, {formalTool === "none" ? "formal disabled" : `${formalTool} + ${formalSolver}`}, {goldenModelTool === "none" ? "golden model disabled" : goldenModelTool}.
                </div>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runClosureLoopAfterVerify || runClosureAnalysis} onChange={(e) => setRunClosureAnalysis(e.target.checked)} disabled={runClosureLoopAfterVerify} className="mt-1" />
                  <span>Run closure analysis after System Sim</span>
                  <span className="mt-1 block text-xs text-slate-500">
                    Starts a linked child workflow when System Sim completes to analyze coverage gaps, failing seeds, and recommended next actions. Required when closure loop is enabled.
                  </span>
                </label>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runClosureLoopAfterVerify} onChange={(e) => setRunClosureLoopAfterVerify(e.target.checked)} className="mt-1" />
                  <span>Run closure loop after System Sim</span>
                  <span className="mt-1 block text-xs text-slate-500">
                    Automatically analyzes gaps, updates plans, adds testcase/seed intents, reruns simulation, and emits a merged coverage trend.
                  </span>
                </label>
                <label className="mt-3 flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={debugFailuresAfterVerify} onChange={(e) => setDebugFailuresAfterVerify(e.target.checked)} className="mt-1" />
                  <span>Debug failing tests after System Sim</span>
                  <span className="mt-1 block text-xs text-slate-500">
                    Runs log-first failure debug for failing testcase/seed pairs before closure-loop coverage chasing.
                  </span>
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

              <HemAutomaticRunControls
                enabled={hemEnabled}
                adaptive={hemAdaptive}
                onEnabledChange={(value) => {
                  setHemEnabled(value);
                  if (!value) setHemAdaptive(false);
                }}
                onAdaptiveChange={setHemAdaptive}
                currentStageLabel="System Sim"
                nextStageLabel="Firmware"
                goal={hemGoal}
                onGoalChange={(value) => setHemGoal(value as SystemHemGoal)}
                goalOptions={SYSTEM_HEM_GOAL_OPTIONS.filter((option) => option.value === "product_demo")}
                stageOptions={systemHemStageOptions(hemGoal, hemStageToggles)}
                onStageToggle={(key, value) => setHemStageToggles((current) => ({ ...current, [key]: value }))}
              />

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

              {false && workflowId ? (
                <div className="hidden">
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
                      {closureChart?.series?.length ? (
                        <div className="mt-4">
                          <div className="text-xs font-semibold uppercase tracking-wide text-violet-200">Coverage trend</div>
                          <div className="mt-2 space-y-2">
                            {[
                              ["functional_coverage_pct", "Functional"],
                              ["code_line_coverage_pct", "Code line"],
                              ["code_branch_coverage_pct", "Branch"],
                              ["code_condition_coverage_pct", "Condition"],
                              ["code_toggle_coverage_pct", "Toggle"],
                            ].map(([key, label]) => {
                              const values = closureChart.series
                                .map((point: any) => Number(point?.[key]))
                                .filter((value: number) => Number.isFinite(value));
                              const latest = values.length ? values[values.length - 1] : null;
                              return (
                                <div key={key} className="grid grid-cols-[110px_minmax(0,1fr)_52px] items-center gap-2 text-xs">
                                  <div className="text-slate-300">{label}</div>
                                  <div className="h-3 overflow-hidden rounded-full bg-slate-800">
                                    <div className="h-full bg-violet-400" style={{ width: `${latest === null ? 0 : Math.max(0, Math.min(100, latest))}%` }} />
                                  </div>
                                  <div className="text-right text-slate-100">{latest === null ? "-" : `${latest}%`}</div>
                                </div>
                              );
                            })}
                          </div>
                          <div className="mt-3 grid grid-cols-3 gap-3 text-xs">
                            {[
                              ["coverage_points_added", "coverage points added"],
                              ["testcase_intents_added", "testcase intents added"],
                              ["seeds_added", "seeds added"],
                            ].map(([key, label]) => {
                              const latest = closureChart.series[closureChart.series.length - 1] || {};
                              return (
                                <div key={key} className="rounded-lg border border-slate-800 bg-black/20 p-2">
                                  <div className="text-slate-400">{label}</div>
                                  <div className="mt-1 text-lg font-semibold text-slate-100">{latest[key] ?? 0}</div>
                                </div>
                              );
                            })}
                          </div>
                          <div className="mt-2 text-xs text-slate-500">Stop reason: {closureChart.stop_reason || "not reported"}</div>
                        </div>
                      ) : null}
                      <div className="mt-3 max-h-52 overflow-auto rounded-lg border border-slate-800 bg-black/30 p-3 font-mono text-xs text-slate-400">
                        {parseLogLines(closureLoopRow?.logs).map((line, index) => (
                          <div key={`${line}-${index}`}>{line}</div>
                        ))}
                      </div>
                    </div>
                  ) : null}
                  <AskThisRunPanel workflowId={workflowId} compact />
                </div>
              ) : null}
            </div>

            <div className="space-y-4">
              {rtlSourceMode === "paste" ? (
                <>
                  <SpecTextBox
                    label="Digital RTL"
                    value={digitalSpecText}
                    onChange={setDigitalSpecText}
                    voiceTitle="Digital RTL Voice Input"
                    voiceLoopType="digital"
                    voiceTarget="System digital RTL"
                    uploadLabel="Upload digital RTL"
                    uploadHelper="Digital Verilog/SystemVerilog module files used by System Sim."
                  />
                  <SpecTextBox
                    label="Analog RTL / behavioral model"
                    value={analogSpecText}
                    onChange={setAnalogSpecText}
                    voiceTitle="Analog Model Voice Input"
                    voiceLoopType="analog"
                    voiceTarget="System analog RTL or behavioral model"
                    uploadLabel="Upload analog model"
                    uploadHelper="Analog macro wrapper or behavioral Verilog/SystemVerilog model used by System Sim."
                  />
                  <SpecTextBox
                    label="SoC RTL"
                    value={socIntegrationSpecText}
                    onChange={setSocIntegrationSpecText}
                    voiceTitle="SoC RTL Voice Input"
                    voiceLoopType="system"
                    voiceTarget="SoC RTL"
                    uploadLabel="Upload SoC RTL"
                    uploadHelper="Top-level SoC wrapper RTL and integration modules."
                  />
                </>
              ) : (
                <div className="rounded-2xl border border-slate-800 bg-black/20 p-4 text-sm text-slate-300">
                  {rtlSourceMode === "from_system_rtl"
                    ? "Using the selected System RTL workflow as the RTL source. Paste boxes are hidden because the run will hydrate RTL, filelists, SoC top, and integration intent from that workflow."
                    : "Using RTL from the repo/path. Paste boxes are hidden because the run will scan the selected path for Verilog/SystemVerilog sources."}
                </div>
              )}
            </div>
          </div>

          {workflowId ? (
            <div className="mt-6 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
              <div>workflow_id: <span className="break-all text-slate-100">{workflowId}</span></div>
              <div>run_id: <span className="break-all text-slate-100">{runId}</span></div>
              <div className="mt-3 flex flex-wrap gap-3">
                <button onClick={downloadZip} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                  Download ZIP (full=1)
                </button>
                <button
                  type="button"
                  onClick={openSystemFirmware}
                  disabled={!readyForFirmware}
                  className="rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                >
                  Open System Firmware
                </button>
                <button
                  type="button"
                  onClick={analyzeClosure}
                  disabled={workflowRow?.status !== "completed" || Boolean(closureWorkflowId)}
                  className="rounded-xl bg-cyan-700 px-4 py-2 font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
                >
                  Analyze Closure
                </button>
                <button
                  type="button"
                  onClick={runClosureLoop}
                  disabled={workflowRow?.status !== "completed" || Boolean(closureLoopWorkflowId)}
                  className="rounded-xl bg-violet-700 px-4 py-2 font-semibold text-white hover:bg-violet-600 disabled:cursor-not-allowed disabled:bg-slate-700"
                >
                  Run Closure Loop
                </button>
              </div>
              <div className="mt-4">
                <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="verification" logs={workflowRow?.logs} />
              </div>
              <HemChildDashboardLinks logs={workflowRow?.logs} />
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
                  {closureChart?.series?.length ? (
                    <div className="mt-4">
                      <div className="text-xs font-semibold uppercase tracking-wide text-violet-200">Coverage trend</div>
                      <div className="mt-2 space-y-2">
                        {[
                          ["functional_coverage_pct", "Functional"],
                          ["code_line_coverage_pct", "Code line"],
                          ["code_branch_coverage_pct", "Branch"],
                          ["code_condition_coverage_pct", "Condition"],
                          ["code_toggle_coverage_pct", "Toggle"],
                        ].map(([key, label]) => {
                          const values = closureChart.series
                            .map((point: any) => Number(point?.[key]))
                            .filter((value: number) => Number.isFinite(value));
                          const latest = values.length ? values[values.length - 1] : null;
                          return (
                            <div key={key} className="grid grid-cols-[110px_minmax(0,1fr)_52px] items-center gap-2 text-xs">
                              <div className="text-slate-300">{label}</div>
                              <div className="h-3 overflow-hidden rounded-full bg-slate-800">
                                <div className="h-full bg-violet-400" style={{ width: `${latest === null ? 0 : Math.max(0, Math.min(100, latest))}%` }} />
                              </div>
                              <div className="text-right text-slate-100">{latest === null ? "-" : `${latest}%`}</div>
                            </div>
                          );
                        })}
                      </div>
                      <div className="mt-3 grid grid-cols-3 gap-3 text-xs">
                        {[
                          ["coverage_points_added", "coverage points added"],
                          ["testcase_intents_added", "testcase intents added"],
                          ["seeds_added", "seeds added"],
                        ].map(([key, label]) => {
                          const latest = closureChart.series[closureChart.series.length - 1] || {};
                          return (
                            <div key={key} className="rounded-lg border border-slate-800 bg-black/20 p-2">
                              <div className="text-slate-400">{label}</div>
                              <div className="mt-1 text-lg font-semibold text-slate-100">{latest[key] ?? 0}</div>
                            </div>
                          );
                        })}
                      </div>
                      <div className="mt-2 text-xs text-slate-500">Stop reason: {closureChart.stop_reason || "not reported"}</div>
                    </div>
                  ) : null}
                  <div className="mt-3 max-h-52 overflow-auto rounded-lg border border-slate-800 bg-black/30 p-3 font-mono text-xs text-slate-400">
                    {parseLogLines(closureLoopRow?.logs).map((line, index) => (
                      <div key={`${line}-${index}`}>{line}</div>
                    ))}
                  </div>
                </div>
              ) : null}
              <div className="mt-4">
                <AskThisRunPanel workflowId={workflowId} compact />
              </div>
            </div>
          ) : null}

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
