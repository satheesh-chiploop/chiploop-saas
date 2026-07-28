"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import { FPGA_BITSTREAM_PREFILL_KEY } from "@/lib/pwmFullStackDemo";
import { FPGA_RUNNABLE_TARGET_OPTIONS, FPGA_TARGET_OPTIONS } from "@/lib/fpgaTargets";
import SpecTextBox from "@/components/SpecTextBox";
import { FiCheck, FiClock, FiCopy, FiLoader, FiX } from "react-icons/fi";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type FieldKind = "source" | "intent" | "rtl" | "sdc" | "timing" | "frequency" | "stage" | "depth" | "notes" | "fpga" | "verify" | "recommendation";

type Props = {
  slug: string;
  title: string;
  subtitle: string;
  runPath: string;
  dashboardStage: "rtl_review" | "constraint_review" | "timing_debug" | "fpga" | "fpga_target_explorer" | "verification";
  fields: FieldKind[];
  defaultSourceMode?: "from_arch2rtl" | "paste" | "repo_path" | "generate_arch2rtl";
  sourceModeLabel?: string;
  closureRunPath?: string;
  fpgaMode?: "bitstream" | "fpga2rtl" | "verify" | "formal" | "synthesis" | "implementation" | "target-explorer";
  referenceRtl?: { label: string; rtl: string; topModule: string; notes?: string };
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter(Boolean);
}

export default function DigitalReviewAppTemplate({ slug, title, subtitle, runPath, dashboardStage, fields, defaultSourceMode, sourceModeLabel, closureRunPath, fpgaMode, referenceRtl }: Props) {
  const router = useRouter();
  const logsRef = useRef<HTMLDivElement | null>(null);

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
  const closureStartedRef = useRef(false);

  const [sourceMode, setSourceMode] = useState<"from_arch2rtl" | "paste" | "repo_path" | "generate_arch2rtl">(defaultSourceMode || "from_arch2rtl");
  const [sourceWorkflowId, setSourceWorkflowId] = useState("");
  const [repoPath, setRepoPath] = useState("");
  const [specText, setSpecText] = useState("");
  const [designIntent, setDesignIntent] = useState("");
  const [rtlText, setRtlText] = useState("");
  const [sdcText, setSdcText] = useState("");
  const [timingText, setTimingText] = useState("");
  const [targetFrequency, setTargetFrequency] = useState(fpgaMode === "target-explorer" ? "75" : "100");
  const [recommendationProfile, setRecommendationProfile] = useState("best_overall");
  const explorerBoards = FPGA_TARGET_OPTIONS;
  const defaultExplorerBoards = FPGA_RUNNABLE_TARGET_OPTIONS.filter((item) => item.tier !== "experimental");
  const [candidateBoards, setCandidateBoards] = useState<string[]>(defaultExplorerBoards.map((item) => item.key));
  const [explorerBaselineSeedCount, setExplorerBaselineSeedCount] = useState("1");
  const [explorerClosureSeedCount, setExplorerClosureSeedCount] = useState("1");
  const [stage, setStage] = useState("auto");
  const [reviewDepth, setReviewDepth] = useState("standard");
  const [notes, setNotes] = useState("");
  const [board, setBoard] = useState("icebreaker");
  const [topModule, setTopModule] = useState("");
  const [pcfText, setPcfText] = useState("");
  const [runFpgaTimingClosureLoop, setRunFpgaTimingClosureLoop] = useState(true);
  const [fpgaClosureMode, setFpgaClosureMode] = useState<"balanced" | "advanced">("balanced");
  const [allowAutomaticRtlTimingRepair, setAllowAutomaticRtlTimingRepair] = useState(false);
  const [contextMode, setContextMode] = useState<"smart" | "full">("smart");
  const [hemEnabled, setHemEnabled] = useState(false);
  const [hemMode, setHemMode] = useState<"fixed" | "adaptive">("fixed");
  const [runFpgaVerification, setRunFpgaVerification] = useState(true);
  const [testIntent, setTestIntent] = useState("Run smoke verification for the FPGA RTL before synthesis. Check reset behavior, basic functional behavior, assertions, and coverage readiness.");
  const [verificationPlan, setVerificationPlan] = useState("");
  const [randomVsDirected, setRandomVsDirected] = useState<"random" | "directed" | "both">("both");
  const [functionalCoverageTarget, setFunctionalCoverageTarget] = useState("90");
  const [lineCoverageTarget, setLineCoverageTarget] = useState("90");
  const [branchCoverageTarget, setBranchCoverageTarget] = useState("80");
  const [toggleCoverageTarget, setToggleCoverageTarget] = useState("80");
  const [conditionCoverageTarget, setConditionCoverageTarget] = useState("80");
  const [simulatorType, setSimulatorType] = useState("verilator");
  const [seedCount, setSeedCount] = useState("10");
  const [enableFormal, setEnableFormal] = useState(fpgaMode === "formal");
  const [formalTool, setFormalTool] = useState<"none" | "symbiyosys">("symbiyosys");
  const [formalSolver, setFormalSolver] = useState<"z3" | "boolector">("z3");
  const [enableGoldenModel, setEnableGoldenModel] = useState(false);
  const [enableFailureDebug, setEnableFailureDebug] = useState(false);
  const [runVerificationClosureLoop, setRunVerificationClosureLoop] = useState(false);
  const [maxVerificationClosureIterations, setMaxVerificationClosureIterations] = useState("1");

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const coverageTargets = useMemo(() => [
    `${functionalCoverageTarget || "90"}% functional`,
    `${lineCoverageTarget || "90"}% line`,
    `${branchCoverageTarget || "80"}% branch`,
    `${toggleCoverageTarget || "80"}% toggle`,
    `${conditionCoverageTarget || "80"}% condition`,
  ].join(", "), [
    functionalCoverageTarget,
    lineCoverageTarget,
    branchCoverageTarget,
    toggleCoverageTarget,
    conditionCoverageTarget,
  ]);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  useEffect(() => {
    (async () => {
      setLoading(true);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace(`/login?next=/apps/${slug}`);
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router, slug]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    if (params.get("reference") && referenceRtl) {
      setSourceMode("paste");
      setRtlText(referenceRtl.rtl);
      setTopModule(referenceRtl.topModule);
      if (referenceRtl.notes) { setNotes(referenceRtl.notes); setDesignIntent(referenceRtl.notes); }
    }
    const source = params.get("from_workflow_id") || params.get("source_workflow_id") || "";
    if (source) {
      setSourceMode("from_arch2rtl");
      setSourceWorkflowId(source);
    }
    if (!fields.includes("fpga")) return;
    const raw = window.localStorage.getItem(FPGA_BITSTREAM_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as Partial<{
        rtlSourceMode: "from_arch2rtl" | "paste" | "repo_path" | "generate_arch2rtl";
        sourceWorkflowId: string;
        repoPath: string;
        specText: string;
        rtlText: string;
        board: string;
        topModule: string;
        targetFrequency: string;
        pcfText: string;
        notes: string;
        hemEnabled: boolean;
        hemMode: "fixed" | "adaptive";
      }>;
      if (prefill.rtlSourceMode) setSourceMode(prefill.rtlSourceMode);
      if (prefill.sourceWorkflowId) setSourceWorkflowId(prefill.sourceWorkflowId);
      if (prefill.repoPath) setRepoPath(prefill.repoPath);
      if (prefill.specText) setSpecText(prefill.specText);
      if (prefill.rtlText) setRtlText(prefill.rtlText);
      if (prefill.board) setBoard(prefill.board);
      if (prefill.topModule) setTopModule(prefill.topModule);
      if (prefill.targetFrequency) setTargetFrequency(prefill.targetFrequency);
      if (prefill.pcfText) setPcfText(prefill.pcfText);
      if (prefill.notes) setNotes(prefill.notes);
      if (typeof prefill.hemEnabled === "boolean") setHemEnabled(prefill.hemEnabled);
      if (prefill.hemMode) setHemMode(prefill.hemMode);
    } catch {
      // Ignore malformed local prefill.
    } finally {
      window.localStorage.removeItem(FPGA_BITSTREAM_PREFILL_KEY);
    }
  }, [loading, referenceRtl]);

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
      .on("postgres_changes", { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` }, (payload) => {
        const row = payload.new as any;
        setWorkflowRow({ id: row.id, status: row.status, phase: row.phase, logs: row.logs, updated_at: row.updated_at });
      })
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
      .on("postgres_changes", { event: "*", schema: "public", table: "workflows", filter: `id=eq.${closureWorkflowId}` }, (payload) => {
        const row = payload.new as any;
        setClosureRow({ id: row.id, status: row.status, phase: row.phase, logs: row.logs, updated_at: row.updated_at });
      })
      .subscribe();

    return () => {
      isActive = false;
      supabase.removeChannel(channel);
    };
  }, [closureWorkflowId]);

  useEffect(() => {
    if (!closureRunPath || !fields.includes("verify") || !runVerificationClosureLoop || closureStartedRef.current) return;
    if (!workflowId || workflowRow?.status !== "completed") return;
    closureStartedRef.current = true;
    void runClosureLoop();
  }, [closureRunPath, fields, runVerificationClosureLoop, workflowId, workflowRow?.status]);

  function authHeaders(): HeadersInit {
    const headers: Record<string, string> = {};
    if (sessionUserId) headers["x-user-id"] = sessionUserId;
    if (accessToken) headers.Authorization = `Bearer ${accessToken}`;
    return headers;
  }

  const canRun = useMemo(() => {
    if (running) return false;
    if (fpgaMode === "target-explorer" && (!candidateBoards.length || !designIntent.trim())) return false;
    if (fpgaMode === "formal") {
      if (sourceMode === "from_arch2rtl") return Boolean(sourceWorkflowId.trim());
      if (sourceMode === "generate_arch2rtl") return Boolean(specText.trim());
      if (sourceMode === "repo_path") return Boolean(repoPath.trim());
      return Boolean(rtlText.trim());
    }
    const integratedFpgaVerify = fields.includes("fpga") && fields.includes("verify");
    if (fields.includes("verify") && (!integratedFpgaVerify || runFpgaVerification) && !testIntent.trim()) return false;
    if (fields.includes("timing")) return Boolean(sourceWorkflowId.trim() || timingText.trim());
    if (sourceMode === "from_arch2rtl") return Boolean(sourceWorkflowId.trim());
    if (sourceMode === "generate_arch2rtl") return Boolean(specText.trim());
    if (sourceMode === "repo_path") return Boolean(repoPath.trim());
    return Boolean(rtlText.trim());
  }, [fields, fpgaMode, running, sourceMode, sourceWorkflowId, repoPath, specText, rtlText, timingText, testIntent, runFpgaVerification, candidateBoards.length, designIntent]);

  async function runClosureLoop() {
    if (!workflowId || !closureRunPath) return;
    try {
      const body: Record<string, any> = {
        source_verify_workflow_id: workflowId,
        coverage_targets: coverageTargets.trim() || undefined,
        seed_count: Number(seedCount || 1),
        seed_budget: Number(seedCount || 1),
        max_iterations: Number(maxVerificationClosureIterations || 1),
        rerun_mode: "coverage_targeted",
        random_vs_directed: randomVsDirected,
        enable_failure_debug: enableFailureDebug,
        toolchain: {
          simulator: simulatorType || "verilator",
          formal: enableFormal ? formalTool : "none",
          formal_solver: formalSolver,
          golden_model: enableGoldenModel ? "enabled" : "none",
        },
      };
      const resp = await fetch(`${API_BASE}${closureRunPath}`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(body),
      });
      if (!resp.ok) {
        const text = await resp.text().catch(() => "");
        throw new Error(`${resp.status} ${resp.statusText}${text ? ` - ${text}` : ""}`);
      }
      const out = await resp.json();
      setClosureWorkflowId(out.workflow_id);
      setClosureRunId(out.run_id);
    } catch (e: any) {
      setErr(e?.message || String(e));
    }
  }

  async function runNow() {
    setErr(null);
    setRunning(true);
    closureStartedRef.current = false;
    setClosureWorkflowId(null);
    setClosureRunId(null);
    setClosureRow(null);
    try {
      const body: Record<string, any> = {
        rtl_source_mode: sourceMode,
        from_workflow_id: sourceMode === "from_arch2rtl" ? sourceWorkflowId.trim() : undefined,
        source_arch2rtl_workflow_id: sourceMode === "from_arch2rtl" ? sourceWorkflowId.trim() : undefined,
        source_workflow_id: sourceWorkflowId.trim() || undefined,
        repo_path: sourceMode === "repo_path" ? repoPath.trim() : undefined,
        spec_text: sourceMode === "generate_arch2rtl" ? specText : fields.includes("intent") ? designIntent.trim() : undefined,
        rtl_text: sourceMode === "paste" ? rtlText : undefined,
        pasted_rtl_files: sourceMode === "paste" && rtlText.trim() ? [{ path: "rtl/review_input.sv", content: rtlText }] : undefined,
        constraints_sdc: sdcText.trim() || undefined,
        timing_report_text: timingText.trim() || undefined,
        target_frequency_mhz: targetFrequency ? Number(targetFrequency) : undefined,
        recommendation_profile: fields.includes("recommendation") ? recommendationProfile : undefined,
        candidate_boards: fpgaMode === "target-explorer" ? candidateBoards : undefined,
        baseline_seed_count: fpgaMode === "target-explorer" ? Number(explorerBaselineSeedCount || 1) : undefined,
        closure_seed_count: fpgaMode === "target-explorer" ? Number(explorerClosureSeedCount || 1) : undefined,
        stage,
        review_depth: reviewDepth,
        board: fields.includes("fpga") ? board : undefined,
        top_module: (fields.includes("fpga") || fpgaMode === "target-explorer") && topModule.trim() ? topModule.trim() : undefined,
        pcf_text: fields.includes("fpga") && pcfText.trim() ? pcfText : undefined,
        lpf_text: fields.includes("fpga") && pcfText.trim() ? pcfText : undefined,
        cst_text: fields.includes("fpga") && pcfText.trim() ? pcfText : undefined,
        notes: notes.trim() || undefined,
        run_fpga_rtl_repair_loop: fields.includes("fpga") ? true : undefined,
        run_fpga_synthesis_closure_loop: fields.includes("fpga") ? runFpgaTimingClosureLoop : undefined,
        max_fpga_synthesis_closure_iterations: fields.includes("fpga") ? (fpgaClosureMode === "advanced" ? 3 : 2) : undefined,
        run_fpga_timing_closure_loop: fields.includes("fpga") ? fpgaMode !== "synthesis" && runFpgaTimingClosureLoop : undefined,
        max_fpga_timing_closure_iterations: fields.includes("fpga") ? (fpgaClosureMode === "advanced" ? 12 : 6) : undefined,
        fpga_closure_mode: fields.includes("fpga") ? fpgaClosureMode : undefined,
        allow_automatic_rtl_timing_repair: fields.includes("fpga") ? fpgaMode !== "synthesis" && allowAutomaticRtlTimingRepair : undefined,
        allow_yosys_flatten: fields.includes("fpga") ? true : undefined,
        allow_nextpnr_seed_sweep: fields.includes("fpga") ? true : undefined,
        allow_frequency_relaxation: fields.includes("fpga") ? true : undefined,
        smart_context_enabled: fields.includes("fpga") ? contextMode === "smart" : undefined,
        context_mode: fields.includes("fpga") ? contextMode : undefined,
        hem_enabled: fields.includes("fpga") ? hemEnabled : undefined,
        hem_mode: fields.includes("fpga") ? hemMode : undefined,
        run_fpga_verification: fields.includes("fpga") && fields.includes("verify") ? runFpgaVerification : undefined,
        run_fpga_verification_closure_loop: fields.includes("fpga") && fields.includes("verify") ? runVerificationClosureLoop : undefined,
        max_fpga_verification_closure_iterations: fields.includes("fpga") && fields.includes("verify") ? Number(maxVerificationClosureIterations || 1) : undefined,
        test_intent: fields.includes("verify") ? testIntent.trim() : undefined,
        verification_plan: fields.includes("verify") && verificationPlan.trim() ? verificationPlan : undefined,
        random_vs_directed: fields.includes("verify") ? randomVsDirected : undefined,
        coverage_targets: fields.includes("verify") && coverageTargets.trim() ? coverageTargets : undefined,
        simulator_type: fields.includes("verify") ? simulatorType : undefined,
        seed_count: fields.includes("verify") ? Number(seedCount || 1) : undefined,
        run_closure_analysis: fields.includes("verify") ? runVerificationClosureLoop || enableFailureDebug : undefined,
        enable_failure_debug: fields.includes("verify") ? enableFailureDebug : undefined,
        failure_debug_options: fields.includes("verify") ? { enabled: enableFailureDebug, rerun_failing_tests: true } : undefined,
        toolchain: fields.includes("verify") ? {
          simulator: simulatorType || "verilator",
          formal: enableFormal ? formalTool : "none",
          formal_solver: formalSolver,
          golden_model: enableGoldenModel ? "enabled" : "none",
        } : undefined,
        toggles: fields.includes("verify") ? {
          enable_formal: enableFormal,
          enable_golden_model: enableGoldenModel,
        } : undefined,
      };
      const resp = await fetch(`${API_BASE}${runPath}`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(body),
      });
      if (!resp.ok) {
        const text = await resp.text().catch(() => "");
        throw new Error(`${resp.status} ${resp.statusText}${text ? ` - ${text}` : ""}`);
      }
      const out = await resp.json();
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

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loading...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto w-full max-w-[1600px] px-4 py-6 sm:px-6 sm:py-8 lg:px-8 lg:py-10">
        <div className="flex items-center justify-between gap-3">
          <button onClick={() => router.push("/apps")} className="rounded-xl border border-slate-700 px-4 py-2 text-slate-200 hover:border-cyan-400">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 text-slate-200 hover:border-cyan-400">
            Studio
          </button>
        </div>

        <section className="mt-6 rounded-2xl border border-cyan-500/40 bg-slate-950/80 p-6 shadow-[0_0_0_1px_rgba(34,211,238,0.08)]">
          <div className="text-sm font-semibold uppercase tracking-[0.18em] text-cyan-300">{fields.includes("fpga") || fpgaMode ? "FPGA Loop" : "Digital Loop"}</div>
          <h1 className="mt-2 text-3xl font-black text-white md:text-4xl">{title}</h1>
          <p className="mt-3 max-w-3xl text-base leading-7 text-slate-300">{subtitle}</p>
          {referenceRtl ? (
            <button
              type="button"
              onClick={() => { setSourceMode("paste"); setRtlText(referenceRtl.rtl); setTopModule(referenceRtl.topModule); if (referenceRtl.notes) { setNotes(referenceRtl.notes); setDesignIntent(referenceRtl.notes); } }}
              className="mt-4 rounded-xl border border-violet-400/50 bg-violet-500/10 px-4 py-2 text-sm font-semibold text-violet-100 hover:border-violet-300"
            >
              {referenceRtl.label}
            </button>
          ) : null}

          <div className="mt-6 space-y-5">
            <div className="space-y-4">
              {fields.includes("source") ? (
                <div className="grid gap-3 md:grid-cols-3">
                  <label className="block">
                    <span className="text-sm text-slate-300">Source</span>
                    <select value={sourceMode} onChange={(e) => setSourceMode(e.target.value as any)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      <option value="from_arch2rtl">Prior workflow</option>
                      {fields.includes("fpga") ? <option value="generate_arch2rtl">{sourceModeLabel || "Generate RTL from design intent"}</option> : null}
                      <option value="paste">Paste RTL</option>
                      <option value="repo_path">Repo/path</option>
                    </select>
                  </label>
                  {sourceMode !== "generate_arch2rtl" ? (
                    <label className="block md:col-span-2">
                      <span className="text-sm text-slate-300">{sourceMode === "repo_path" ? "Repo/path" : "Source workflow ID"}</span>
                      <input
                        value={sourceMode === "repo_path" ? repoPath : sourceWorkflowId}
                        onChange={(e) => (sourceMode === "repo_path" ? setRepoPath(e.target.value) : setSourceWorkflowId(e.target.value))}
                        className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white"
                        placeholder={sourceMode === "repo_path" ? "C:/path/to/repo or /repo/path" : "Workflow ID"}
                      />
                    </label>
                  ) : (
                    <div className="rounded-xl border border-cyan-500/30 bg-cyan-950/10 px-4 py-3 text-sm leading-6 text-cyan-100 md:col-span-2">
                      ChipLoop will create RTL first, then continue through FPGA implementation for the selected board.
                    </div>
                  )}
                </div>
              ) : null}

              {fields.includes("intent") ? (
                <SpecTextBox
                  label="Design intent"
                  value={designIntent}
                  onChange={setDesignIntent}
                  rows={6}
                  required
                  voiceTitle="FPGA Explorer Design Intent Voice Input"
                  voiceLoopType="fpga"
                  voiceTarget="FPGA target exploration design intent, interfaces, workload, and implementation priorities"
                  uploadLabel="Upload design intent"
                  uploadHelper="Upload a text, Markdown, JSON, or YAML design-intent document. Choose Replace or Append before applying it."
                  placeholder="Describe what the RTL implements, its interfaces, workload, and important implementation priorities."
                />
              ) : null}

              {fields.includes("fpga") && sourceMode === "generate_arch2rtl" ? (
                <SpecTextBox
                  label="Design intent"
                  value={specText}
                  onChange={setSpecText}
                  rows={9}
                  voiceTitle="FPGA Design Intent Voice Input"
                  voiceLoopType="fpga"
                  voiceTarget="FPGA prototype design intent for Arch2RTL generation"
                  uploadLabel="Upload spec"
                  uploadHelper="Upload a text, Markdown, or small spec file that describes the FPGA prototype."
                  placeholder="Describe the block you want ChipLoop to generate as RTL before FPGA prototyping."
                  textareaClassName="w-full resize-y bg-transparent p-1 text-sm text-slate-100 outline-none"
                />
              ) : null}

              {(fields.includes("fpga") || fpgaMode === "target-explorer") && (fields.includes("rtl") || sourceMode === "paste") ? (
                <SpecTextBox
                  label="RTL / FPGA source"
                  value={rtlText}
                  onChange={setRtlText}
                  rows={9}
                  voiceTitle="FPGA RTL Voice Input"
                  voiceLoopType="fpga"
                  voiceTarget="RTL source, board notes, or FPGA prototype intent"
                  uploadLabel="Upload RTL"
                  uploadHelper="Upload Verilog/SystemVerilog, board notes, or small source snippets."
                  placeholder="Paste Verilog/SystemVerilog RTL or upload source files."
                  textareaClassName="w-full resize-y bg-transparent p-1 font-mono text-sm text-slate-100 outline-none"
                />
              ) : fields.includes("rtl") || sourceMode === "paste" ? (
                <label className="block">
                  <span className="text-sm text-slate-300">RTL text</span>
                  <textarea value={rtlText} onChange={(e) => setRtlText(e.target.value)} rows={8} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              {fields.includes("sdc") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Constraints SDC</span>
                  <textarea value={sdcText} onChange={(e) => setSdcText(e.target.value)} rows={7} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              {fields.includes("timing") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Timing report text</span>
                  <textarea value={timingText} onChange={(e) => setTimingText(e.target.value)} rows={9} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              <div className="grid gap-3 md:grid-cols-3">
                {fpgaMode === "target-explorer" ? (
                  <div className="md:col-span-3">
                    <div className="flex flex-wrap items-center justify-between gap-2">
                      <div>
                        <div className="text-sm font-semibold text-slate-200">Boards and devices to explore *</div>
                        <div className="mt-1 text-xs text-slate-500">Only selected targets run synthesis and place-and-route.</div>
                      </div>
                      <div className="flex gap-2">
                        <button type="button" onClick={() => setCandidateBoards(FPGA_RUNNABLE_TARGET_OPTIONS.map((item) => item.key))} className="rounded-lg border border-slate-700 px-3 py-1.5 text-xs text-slate-300 hover:border-cyan-400/60">Select runnable</button>
                        <button type="button" onClick={() => setCandidateBoards([])} className="rounded-lg border border-slate-700 px-3 py-1.5 text-xs text-slate-300 hover:border-cyan-400/60">Clear</button>
                      </div>
                    </div>
                    <div className="mt-3 max-h-56 overflow-y-auto rounded-xl border border-slate-800 bg-black/25 p-2">
                      <div className="grid gap-2 sm:grid-cols-2 lg:grid-cols-3">
                        {explorerBoards.map((item) => {
                          const selected = candidateBoards.includes(item.key);
                          return (
                            <label key={item.key} title={item.reason} className={`flex items-start gap-3 rounded-lg border p-3 transition ${item.tier === "unavailable" ? "cursor-not-allowed border-slate-900 opacity-50" : selected ? "cursor-pointer border-cyan-400/50 bg-cyan-500/10" : "cursor-pointer border-slate-800 bg-black/20 hover:border-slate-700"}`}>
                              <input type="checkbox" disabled={item.tier === "unavailable"} checked={selected} onChange={() => setCandidateBoards((current) => selected ? current.filter((key) => key !== item.key) : [...current, item.key])} className="mt-1" />
                              <span><span className="block text-sm font-semibold text-slate-100">{item.label}</span><span className="mt-0.5 block text-xs text-slate-500">{item.detail}</span><span className="mt-1 block text-[11px] text-slate-600">{item.segments} · {item.tier}</span></span>
                            </label>
                          );
                        })}
                      </div>
                    </div>
                    <div className={`mt-2 text-xs ${candidateBoards.length ? "text-cyan-300" : "text-rose-300"}`}>{candidateBoards.length ? `${candidateBoards.length} target${candidateBoards.length === 1 ? "" : "s"} selected` : "Select at least one target."}</div>
                  </div>
                ) : null}
                {fields.includes("fpga") && fpgaMode !== "target-explorer" ? (
                  <>
                    <label className="block">
                      <span className="text-sm text-slate-300">Board</span>
                      <select value={board} onChange={(e) => setBoard(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                        {FPGA_TARGET_OPTIONS.map((item) => (
                          <option key={item.key} value={item.key} disabled={item.tier === "unavailable"}>{item.label} — {item.family} ({item.tier})</option>
                        ))}
                      </select>
                    </label>
                    <label className="block">
                      <span className="text-sm text-slate-300">Top module</span>
                      <input value={topModule} onChange={(e) => setTopModule(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" placeholder="auto-detect if blank" />
                    </label>
                  </>
                ) : null}
                {fpgaMode === "target-explorer" ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Top module</span>
                    <input value={topModule} onChange={(e) => setTopModule(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" placeholder="auto-detect if blank" />
                  </label>
                ) : null}
                {fields.includes("frequency") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Target MHz</span>
                    <input value={targetFrequency} onChange={(e) => setTargetFrequency(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                  </label>
                ) : null}
                {fpgaMode === "target-explorer" ? (
                  <>
                    <label className="block">
                      <span className="text-sm text-slate-300">Baseline seeds</span>
                      <input type="number" min="1" max="10" step="1" value={explorerBaselineSeedCount} onChange={(e) => setExplorerBaselineSeedCount(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                      <span className="mt-1 block text-xs text-slate-500">Default 1. Runs for every unique selected device.</span>
                    </label>
                    <label className="block">
                      <span className="text-sm text-slate-300">Closure seeds</span>
                      <input type="number" min="1" max="10" step="1" value={explorerClosureSeedCount} onChange={(e) => setExplorerClosureSeedCount(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                      <span className="mt-1 block text-xs text-slate-500">Default 1. Used only after a routed timing miss.</span>
                    </label>
                  </>
                ) : null}
                {fields.includes("recommendation") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Primary recommendation</span>
                    <select value={recommendationProfile} onChange={(e) => setRecommendationProfile(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      <option value="best_overall">Best overall</option>
                      <option value="best_performance">Best performance</option>
                      <option value="best_low_cost">Best low-cost variant</option>
                      <option value="best_for_growth">Best for growth</option>
                    </select>
                    <span className="mt-1 block text-xs text-slate-500">All four recommendations are still generated and selectable after the run.</span>
                  </label>
                ) : null}
                {fields.includes("stage") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Stage</span>
                    <select value={stage} onChange={(e) => setStage(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      {["auto", "synthesis", "preplace", "postplace", "postcts", "postroute", "postfill"].map((item) => <option key={item} value={item}>{item}</option>)}
                    </select>
                  </label>
                ) : null}
                {fields.includes("depth") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Review depth</span>
                    <select value={reviewDepth} onChange={(e) => setReviewDepth(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      <option value="quick">quick</option>
                      <option value="standard">standard</option>
                      <option value="deep">deep</option>
                    </select>
                  </label>
                ) : null}
              </div>

              {fields.includes("fpga") ? (
                <div className="space-y-4">
                  <SpecTextBox
                    label="Pin constraints PCF / LPF / CST"
                    value={pcfText}
                    onChange={setPcfText}
                    rows={7}
                    voiceTitle="FPGA Constraint Voice Input"
                    voiceLoopType="fpga"
                    voiceTarget="PCF, LPF, or CST pin constraints and board pin mapping"
                    uploadLabel="Upload constraints"
                    uploadHelper="Upload Lattice PCF/LPF or Gowin CST constraints and board pin notes."
                    placeholder={'set_io clk 35\nset_io reset_n 10\nset_io led 99'}
                    textareaClassName="w-full resize-y bg-transparent p-1 font-mono text-sm text-slate-100 outline-none"
                  />
                  <span className="block text-xs text-amber-200">Use real board pin names before programming hardware. Blank PCF creates a starter file only.</span>

                  <div className="rounded-2xl border border-cyan-500/30 bg-cyan-950/10 p-4">
                    <div className="flex flex-wrap items-start justify-between gap-3">
                      <div>
                        <div className="text-sm font-bold text-cyan-200">{fpgaMode === "synthesis" ? "Synthesis closure" : "Timing closure"}</div>
                        <div className="mt-1 text-xs text-slate-400">{fpgaMode === "synthesis" ? "ChipLoop automatically explores safe Yosys synthesis strategies." : "ChipLoop automatically explores seeds and safe synthesis strategies, then locks the winning implementation."}</div>
                      </div>
                      <label className="flex items-center gap-2 text-sm font-semibold text-white">
                        <input type="checkbox" checked={runFpgaTimingClosureLoop} onChange={(e) => setRunFpgaTimingClosureLoop(e.target.checked)} />
                        Enable
                      </label>
                    </div>
                    <div className="mt-4 grid gap-3 md:grid-cols-2">
                      <label className="block">
                        <span className="text-xs uppercase tracking-wide text-slate-400">Closure mode</span>
                        <select value={fpgaClosureMode} onChange={(e) => setFpgaClosureMode(e.target.value as "balanced" | "advanced")} disabled={!runFpgaTimingClosureLoop} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                          <option value="balanced">Balanced</option>
                          <option value="advanced">Advanced</option>
                        </select>
                        <span className="mt-1 block text-xs text-slate-500">{fpgaClosureMode === "advanced" ? "Wider implementation search for difficult paths." : "Good closure coverage with moderate runtime."}</span>
                      </label>
                      {fpgaMode !== "synthesis" ? <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/30 p-3 text-sm text-slate-200">
                        <input type="checkbox" checked={allowAutomaticRtlTimingRepair} onChange={(e) => setAllowAutomaticRtlTimingRepair(e.target.checked)} disabled={!runFpgaTimingClosureLoop} className="mt-1 disabled:opacity-50" />
                        <span>
                          <span className="block font-semibold text-white">Automatic RTL timing repair</span>
                          <span className="text-slate-400">Off by default. If used, ChipLoop reruns verification and reports before-versus-after timing.</span>
                        </span>
                      </label> : <div className="rounded-xl border border-slate-800 bg-black/30 p-3 text-sm text-slate-400">RTL timing repair becomes available in FPGA Implementation and Bitstream, after place-and-route timing evidence exists.</div>}
                    </div>
                    <details className="mt-3 rounded-xl border border-slate-800 bg-black/20 px-3 py-2">
                      <summary className="cursor-pointer text-xs font-semibold uppercase tracking-wide text-slate-400">Run intelligence</summary>
                      <div className="mt-3 grid gap-3 md:grid-cols-2">
                        <label className="block">
                          <span className="text-xs text-slate-400">Context</span>
                          <select value={contextMode} onChange={(e) => setContextMode(e.target.value as "smart" | "full")} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white"><option value="smart">Smart</option><option value="full">Full</option></select>
                        </label>
                        <label className="flex items-center gap-2 self-end pb-2 text-sm text-slate-300"><input type="checkbox" checked={hemEnabled} onChange={(e) => setHemEnabled(e.target.checked)} /> Remember run context</label>
                      </div>
                    </details>
                  </div>
                </div>
              ) : null}

              {fields.includes("verify") ? (
                <div className="rounded-2xl border border-cyan-500/30 bg-cyan-950/10 p-4">
                  <div className="flex flex-wrap items-start justify-between gap-3">
                    <div>
                      <div className="text-sm font-bold text-cyan-200">{fpgaMode === "formal" ? "FPGA formal verification" : "FPGA verification"}</div>
                      {fpgaMode !== "formal" ? <div className="mt-1 text-xs text-slate-400">Run simulation and coverage before implementation; optionally iterate on failures and coverage gaps.</div> : null}
                    </div>
                    {fpgaMode !== "formal" ? (
                      <div className="flex flex-wrap items-center gap-4 rounded-xl border border-slate-800 bg-black/25 px-3 py-2">
                        <label className="flex items-center gap-2 text-sm font-semibold text-slate-200">
                          <input type="checkbox" checked={runFpgaVerification} onChange={(e) => setRunFpgaVerification(e.target.checked)} />
                          Enable verification
                        </label>
                        <label className="flex items-center gap-2 text-sm font-semibold text-slate-200">
                          <input type="checkbox" checked={runVerificationClosureLoop} onChange={(e) => setRunVerificationClosureLoop(e.target.checked)} disabled={!runFpgaVerification} className="disabled:opacity-50" />
                          Enable verification closure
                        </label>
                      </div>
                    ) : null}
                  </div>
                  {fpgaMode !== "formal" ? (
                    <>
                      <fieldset disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-3 grid gap-3 disabled:opacity-50 md:grid-cols-2">
                        <SpecTextBox
                          label="Test intent"
                          value={testIntent}
                          onChange={setTestIntent}
                          rows={5}
                          required
                          voiceTitle="FPGA Test Intent Voice Input"
                          voiceLoopType="fpga"
                          voiceTarget="FPGA verification test intent, scenarios, assertions, and expected behavior"
                          uploadLabel="Upload test intent"
                          uploadHelper="Upload a text, Markdown, JSON, or YAML test-intent document. Choose Replace or Append before applying it."
                          placeholder="Describe smoke tests, directed tests, assertions, and expected behavior."
                        />
                        <SpecTextBox
                          label="Verification plan"
                          value={verificationPlan}
                          onChange={setVerificationPlan}
                          rows={5}
                          voiceTitle="FPGA Verification Plan Voice Input"
                          voiceLoopType="fpga"
                          voiceTarget="FPGA verification plan, test strategy, checkers, assertions, and closure approach"
                          uploadLabel="Upload verification plan"
                          uploadHelper="Upload a reviewer-authored verification plan. Choose Replace or Append before applying it."
                          placeholder="Optional plan. Leave blank for ChipLoop to generate it from the design and test intent."
                        />
                      </fieldset>
                      <div className="mt-3 grid gap-3 md:grid-cols-4">
                        <label className="block">
                          <span className="text-xs uppercase tracking-wide text-slate-400">Stimulus</span>
                          <select value={randomVsDirected} onChange={(e) => setRandomVsDirected(e.target.value as any)} disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                            <option value="both">Both</option>
                            <option value="directed">Directed</option>
                            <option value="random">Random</option>
                          </select>
                        </label>
                        <label className="block">
                          <span className="text-xs uppercase tracking-wide text-slate-400">Simulator</span>
                          <select value={simulatorType} onChange={(e) => setSimulatorType(e.target.value)} disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                            <option value="verilator">Verilator</option>
                            <option value="icarus">Icarus</option>
                          </select>
                        </label>
                        <label className="block">
                          <span className="text-xs uppercase tracking-wide text-slate-400">Seeds</span>
                          <input value={seedCount} onChange={(e) => setSeedCount(e.target.value)} disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50" />
                        </label>
                        <label className="block">
                          <span className="text-xs uppercase tracking-wide text-slate-400">Verification closure tries</span>
                          <input value={maxVerificationClosureIterations} onChange={(e) => setMaxVerificationClosureIterations(e.target.value)} disabled={!runFpgaVerification || !runVerificationClosureLoop} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50" />
                        </label>
                      </div>
                      <fieldset disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-4 rounded-xl border border-slate-800 bg-black/20 p-3 disabled:opacity-50">
                        <legend className="px-1 text-sm font-semibold text-slate-200">Coverage targets</legend>
                        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-5">
                          {[
                            ["Functional", functionalCoverageTarget, setFunctionalCoverageTarget],
                            ["Line", lineCoverageTarget, setLineCoverageTarget],
                            ["Branch", branchCoverageTarget, setBranchCoverageTarget],
                            ["Toggle", toggleCoverageTarget, setToggleCoverageTarget],
                            ["Condition", conditionCoverageTarget, setConditionCoverageTarget],
                          ].map(([label, value, setter]) => (
                            <label key={String(label)} className="block">
                              <span className="text-xs uppercase tracking-wide text-slate-400">{String(label)}</span>
                              <div className="mt-1 flex items-center rounded-lg border border-slate-700 bg-black/40 focus-within:border-cyan-400/70">
                                <input
                                  type="number"
                                  min="0"
                                  max="100"
                                  step="1"
                                  inputMode="decimal"
                                  value={String(value)}
                                  onChange={(event) => (setter as (next: string) => void)(event.target.value)}
                                  className="min-w-0 flex-1 bg-transparent px-3 py-2 text-white outline-none"
                                  aria-label={`${String(label)} coverage target percentage`}
                                />
                                <span className="pr-3 text-sm text-slate-500">%</span>
                              </div>
                            </label>
                          ))}
                        </div>
                        <div className="mt-2 text-xs text-slate-500">ChipLoop uses these thresholds for coverage-gap analysis and closure decisions.</div>
                      </fieldset>
                    </>
                  ) : null}
                  <div className="mt-3 grid gap-3 md:grid-cols-3">
                    <label className="block">
                      <span className="text-xs uppercase tracking-wide text-slate-400">Formal tool</span>
                      <select value={enableFormal ? formalTool : "none"} onChange={(e) => { const value = e.target.value as "none" | "symbiyosys"; setEnableFormal(value !== "none"); if (value !== "none") setFormalTool(value); }} disabled={fields.includes("fpga") && !runFpgaVerification} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                        <option value="none">Disabled</option>
                        <option value="symbiyosys">SymbiYosys (sby)</option>
                      </select>
                    </label>
                    <label className="block">
                      <span className="text-xs uppercase tracking-wide text-slate-400">Formal solver</span>
                      <select value={formalSolver} onChange={(e) => setFormalSolver(e.target.value as "z3" | "boolector")} disabled={!enableFormal || (fields.includes("fpga") && !runFpgaVerification)} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                        <option value="z3">Z3</option>
                        <option value="boolector">Boolector</option>
                      </select>
                    </label>
                  </div>
                  <div className="mt-3 grid gap-3 md:grid-cols-4">
                    {fpgaMode !== "formal" ? <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={enableGoldenModel} onChange={(e) => setEnableGoldenModel(e.target.checked)} disabled={fields.includes("fpga") && !runFpgaVerification} /> Golden model</label> : null}
                    {fpgaMode !== "formal" ? <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={enableFailureDebug} onChange={(e) => setEnableFailureDebug(e.target.checked)} disabled={fields.includes("fpga") && !runFpgaVerification} /> Failure debug</label> : null}
                  </div>
                </div>
              ) : null}

              {fpgaMode === "target-explorer" ? (
                <div className="rounded-xl border border-emerald-500/25 bg-emerald-950/10 p-3 text-sm text-emerald-100">
                  Before exploration, ChipLoop ingests the RTL and runs the FPGA lint/compile quality gate. A failing available lint tool blocks synthesis; tool-unavailable evidence is reported explicitly.
                </div>
              ) : null}

              {fields.includes("notes") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Notes</span>
                  <textarea value={notes} onChange={(e) => setNotes(e.target.value)} rows={3} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                </label>
              ) : null}

              {err ? <div className="rounded-xl border border-rose-500/40 bg-rose-950/40 p-3 text-sm text-rose-200">{err}</div> : null}

              <div className="flex flex-wrap items-center justify-center gap-3 rounded-2xl border border-cyan-400/25 bg-gradient-to-r from-cyan-950/35 via-slate-950/70 to-violet-950/25 p-4 shadow-[0_18px_60px_rgba(8,145,178,0.08)]">
                <button disabled={!canRun} onClick={runNow} className="min-h-11 w-36 rounded-xl bg-gradient-to-r from-cyan-300 to-cyan-400 px-5 py-2.5 text-sm font-black text-slate-950 shadow-[0_10px_35px_rgba(34,211,238,0.22)] transition hover:from-cyan-200 hover:to-cyan-300 disabled:cursor-not-allowed disabled:opacity-50">
                  {running ? "Running..." : "Run"}
                </button>
                <button disabled={!workflowId} onClick={downloadZip} className="min-h-11 w-36 rounded-xl border border-slate-700 bg-black/30 px-5 py-2.5 text-sm font-semibold text-slate-200 transition hover:border-cyan-400/60 hover:text-cyan-100 disabled:opacity-50">
                  Download ZIP
                </button>
              </div>
            </div>

            <aside className="overflow-hidden rounded-2xl border border-slate-700/80 bg-black/35 shadow-[0_20px_70px_rgba(0,0,0,0.28)]">
              <div className="flex flex-col gap-4 border-b border-slate-800 bg-gradient-to-r from-slate-900/90 via-slate-950/90 to-cyan-950/20 p-4 sm:flex-row sm:items-center sm:justify-between sm:p-5">
                <div className="min-w-0">
                  <div className="text-xs font-semibold uppercase tracking-[0.16em] text-cyan-300">Workflow ID</div>
                  <div className="mt-2 break-all font-mono text-sm text-slate-100 sm:text-base">{workflowId || "Created after you start the run"}</div>
                  {runId ? <div className="mt-2 break-all font-mono text-xs text-slate-500">Run ID: {runId}</div> : null}
                </div>
                <div className="flex shrink-0 items-center gap-3">
                  {workflowId ? (
                    <button
                      type="button"
                      onClick={() => navigator.clipboard?.writeText(workflowId)}
                      className="inline-flex h-9 w-9 items-center justify-center rounded-lg border border-slate-700 bg-black/25 text-slate-300 transition hover:border-cyan-400/60 hover:text-cyan-100"
                      title="Copy workflow ID"
                      aria-label="Copy workflow ID"
                    >
                      <FiCopy aria-hidden="true" className="h-4 w-4" />
                    </button>
                  ) : null}
                  <div
                    className={`inline-flex h-9 w-9 items-center justify-center rounded-full border bg-black/30 ${running ? "border-cyan-400/60 text-cyan-300" : workflowRow?.status === "failed" ? "border-rose-500/60 text-rose-400" : workflowRow?.status === "completed" ? "border-emerald-500/60 text-emerald-400" : "border-slate-700 text-slate-500"}`}
                    title={workflowRow?.status || (running ? "Running" : "Idle")}
                    role="status"
                    aria-label={`Workflow status: ${workflowRow?.status || (running ? "running" : "idle")}`}
                  >
                    {running ? <FiLoader aria-hidden="true" className="h-4 w-4 animate-spin" /> : workflowRow?.status === "failed" ? <FiX aria-hidden="true" className="h-4 w-4" /> : workflowRow?.status === "completed" ? <FiCheck aria-hidden="true" className="h-4 w-4" /> : <FiClock aria-hidden="true" className="h-4 w-4" />}
                  </div>
                </div>
              </div>
              <div className="flex items-center justify-between border-b border-slate-900 bg-black/45 px-4 py-3 sm:px-5">
                <div className="text-sm font-bold text-white">Run log</div>
                <div className="text-xs text-slate-500">{logLines.length ? `${logLines.length} lines` : "Waiting to start"}</div>
              </div>
              <div ref={logsRef} className="h-[280px] overflow-auto bg-[#03070d] p-4 font-mono text-xs leading-6 text-slate-300 sm:h-[360px] sm:p-5 lg:h-[440px]">
                {logLines.length ? logLines.map((line, idx) => <div className="border-b border-slate-900/60 py-0.5 last:border-0" key={`${idx}-${line}`}>{line}</div>) : <div className="flex h-full items-center justify-center text-center text-slate-500">Run activity will appear here after you start {title}.</div>}
              </div>
            </aside>
          </div>
        </section>

        {workflowId ? (
          <section className="mt-6 space-y-6">
            <WorkflowEvidenceDashboard
              workflowId={workflowId}
              status={workflowRow?.status}
              stage={dashboardStage}
              logs={workflowRow?.logs}
              linkedHeatmaps={closureWorkflowId ? [{ label: "FPGA Verification Closure Loop", workflowId: closureWorkflowId, status: closureRow?.status, logs: closureRow?.logs }] : undefined}
            />
            {closureWorkflowId ? (
              <div className="rounded-2xl border border-violet-500/30 bg-violet-950/15 p-4 text-sm text-slate-300">
                <div className="font-semibold text-violet-200">FPGA Verification Closure Loop</div>
                <div className="mt-2">workflow_id: <span className="break-all text-slate-100">{closureWorkflowId}</span></div>
                <div>run_id: <span className="break-all text-slate-100">{closureRunId}</span></div>
                <div>status: <span className="text-slate-100">{closureRow?.status || "queued"}</span></div>
              </div>
            ) : null}
            <AskThisRunPanel workflowId={workflowId} />
          </section>
        ) : null}
      </div>
    </main>
  );
}
