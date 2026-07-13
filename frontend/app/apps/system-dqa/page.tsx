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
import SpecTextBox from "@/components/SpecTextBox";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import { DESIGN_CHAIN_CONTEXT_KEY, type DesignChainContext } from "@/lib/pwmFullStackDemo";

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
  return logs.split("\n").map((line) => line.trimEnd()).filter((line) => line.trim().length > 0);
}

export default function SystemDQAAppPage() {
  const router = useRouter();
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  const [projectName, setProjectName] = useState("");
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");
  const [digitalSpecText, setDigitalSpecText] = useState("");
  const [analogSpecText, setAnalogSpecText] = useState("");
  const [socIntegrationSpecText, setSocIntegrationSpecText] = useState("");
  const [runSpec2RtlCheck, setRunSpec2RtlCheck] = useState(false);
  const [runLint, setRunLint] = useState(true);
  const [runCdc, setRunCdc] = useState(true);
  const [runReset, setRunReset] = useState(true);
  const [runSynthesisReadiness, setRunSynthesisReadiness] = useState(true);
  const [nextFlow, setNextFlow] = useState<"system-synthesis" | "system-pd" | "system-firmware">("system-synthesis");
  const [hemEnabled, setHemEnabled] = useState(false);
  const [hemAdaptive, setHemAdaptive] = useState(false);
  const [hemGoal, setHemGoal] = useState<SystemHemGoal>("product_demo");
  const [hemStageToggles, setHemStageToggles] = useState({ ...SYSTEM_HEM_DEFAULT_STAGE_TOGGLES });

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
        router.replace("/login?next=/apps/system-dqa");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    try {
      const context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
      if (context.systemRtlWorkflowId) setSystemRtlWorkflowId(context.systemRtlWorkflowId);
    } catch {
      // ignore malformed handoff context
    }
  }, [loading]);

  useEffect(() => {
    if (!workflowId) return;
    let active = true;
    const fetchWorkflow = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .maybeSingle();
      if (active && !error && data) setWorkflowRow(data as WorkflowRow);
    };
    void fetchWorkflow();
    const interval = window.setInterval(() => void fetchWorkflow(), 2500);
    const channel = supabase.channel(`wf-${workflowId}`).on(
      "postgres_changes",
      { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
      (payload) => setWorkflowRow(payload.new as WorkflowRow),
    ).subscribe();
    return () => {
      active = false;
      window.clearInterval(interval);
      supabase.removeChannel(channel);
    };
  }, [workflowId]);

  const canRun = useMemo(() => {
    if (running) return false;
    if (!runLint && !runCdc && !runReset && !runSynthesisReadiness) return false;
    if (systemRtlWorkflowId.trim()) return true;
    return Boolean(digitalSpecText.trim() && analogSpecText.trim() && socIntegrationSpecText.trim());
  }, [running, runLint, runCdc, runReset, runSynthesisReadiness, systemRtlWorkflowId, digitalSpecText, analogSpecText, socIntegrationSpecText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/system/dqa/run", {
        project_name: projectName || undefined,
        rtl_source_mode: systemRtlWorkflowId.trim() ? "from_system_rtl" : undefined,
        system_rtl_workflow_id: systemRtlWorkflowId.trim() || undefined,
        from_workflow_id: systemRtlWorkflowId.trim() || undefined,
        digital_spec_text: digitalSpecText,
        analog_spec_text: analogSpecText,
        soc_integration_spec_text: socIntegrationSpecText,
        toggles: {
          run_spec2rtl_check: runSpec2RtlCheck,
          run_lint: runLint,
          run_cdc: runCdc,
          run_reset: runReset,
          run_synthesis_readiness: runSynthesisReadiness,
        },
        hem_enabled: hemEnabled,
        hem_mode: hemAdaptive ? "adaptive" : "fixed",
        hem_goal: hemGoal,
        hem_stage_toggles: hemStageToggles,
      });
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

  function openNextFlow() {
    if (!workflowId || typeof window === "undefined") return;
    const sourceSystemRtlWorkflowId = systemRtlWorkflowId.trim() || workflowId;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.systemRtlWorkflowId = sourceSystemRtlWorkflowId;
    context.systemDqaWorkflowId = workflowId;
    context.systemDqaRunId = runId || undefined;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    router.push(`/apps/${nextFlow}?handoff=1&from_workflow_id=${encodeURIComponent(sourceSystemRtlWorkflowId)}&parent_workflow_id=${encodeURIComponent(workflowId)}`);
  }

  if (loading) {
    return <main className="flex min-h-screen items-center justify-center bg-black text-white">Loading...</main>;
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-[1440px] px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Back to Apps</button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">Studio</button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">System DQA</h1>
          <p className="mt-2 text-slate-300">Run lint, CDC, reset-integrity, and synthesis-readiness quality checks on integrated System RTL.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name</label>
              <input value={projectName} onChange={(e) => setProjectName(e.target.value)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">
                System RTL workflow id
                <input value={systemRtlWorkflowId} onChange={(e) => setSystemRtlWorkflowId(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Optional: continue from System RTL" />
              </label>

              <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                <input type="checkbox" checked={runSpec2RtlCheck} onChange={(e) => setRunSpec2RtlCheck(e.target.checked)} className="mt-1" />
                <span>Run Spec2RTL conformance before quality checks</span>
              </label>

              <div className="overflow-hidden rounded-xl border border-slate-800 bg-black/20">
                <div className="border-b border-slate-800 px-4 py-3 text-sm font-semibold text-slate-100">Tools and checks before run</div>
                <div className="grid grid-cols-[auto_1fr_1fr] border-b border-slate-800 px-4 py-2 text-xs font-semibold uppercase text-slate-400">
                  <div>Use</div>
                  <div>Check</div>
                  <div>Primary tool</div>
                </div>
                {[
                  { label: "RTL lint", tool: "Verilator", checked: runLint, set: setRunLint },
                  { label: "CDC analysis", tool: "Heuristic scan", checked: runCdc, set: setRunCdc },
                  { label: "Reset integrity", tool: "Heuristic scan", checked: runReset, set: setRunReset },
                  { label: "Synthesis readiness", tool: "Yosys", checked: runSynthesisReadiness, set: setRunSynthesisReadiness },
                ].map((item) => (
                  <label key={item.label} className="grid grid-cols-[auto_1fr_1fr] items-center gap-3 border-b border-slate-800 px-4 py-3 text-sm last:border-b-0">
                    <input type="checkbox" checked={item.checked} onChange={(e) => item.set(e.target.checked)} />
                    <span className="text-slate-200">{item.label}</span>
                    <span className="text-cyan-100">{item.tool}</span>
                  </label>
                ))}
              </div>

              <HemAutomaticRunControls
                enabled={hemEnabled}
                adaptive={hemAdaptive}
                onEnabledChange={(value) => {
                  setHemEnabled(value);
                  if (!value) setHemAdaptive(false);
                }}
                onAdaptiveChange={setHemAdaptive}
                currentStageLabel="System DQA"
                nextStageLabel={hemGoal === "implementation" ? "System Synthesis" : "System Sim"}
                goal={hemGoal}
                onGoalChange={(value) => setHemGoal(value as SystemHemGoal)}
                goalOptions={SYSTEM_HEM_GOAL_OPTIONS}
                stageOptions={systemHemStageOptions(hemGoal, hemStageToggles)}
                onStageToggle={(key, value) => setHemStageToggles((current) => ({ ...current, [key]: value }))}
              />

              <button onClick={runNow} disabled={!canRun} className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${canRun ? "bg-amber-600 hover:bg-amber-500" : "cursor-not-allowed bg-slate-700"}`}>
                {running ? "Starting..." : "Run System DQA"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}
            </div>

            <div className="space-y-4">
              <SpecTextBox label="Digital specification" required={!systemRtlWorkflowId.trim()} value={digitalSpecText} onChange={setDigitalSpecText} rows={6} voiceTitle="Digital Voice Spec" voiceLoopType="digital" voiceTarget="System digital spec" uploadLabel="Upload digital spec" uploadHelper="Used only when no System RTL workflow id is supplied." placeholder="Paste digital spec here..." />
              <SpecTextBox label="Analog specification" required={!systemRtlWorkflowId.trim()} value={analogSpecText} onChange={setAnalogSpecText} rows={6} voiceTitle="Analog Voice Spec" voiceLoopType="analog" voiceTarget="System analog spec" uploadLabel="Upload analog spec" uploadHelper="Used only when no System RTL workflow id is supplied." placeholder="Paste analog spec here..." />
              <SpecTextBox label="SoC integration specification" required={!systemRtlWorkflowId.trim()} value={socIntegrationSpecText} onChange={setSocIntegrationSpecText} rows={6} voiceTitle="SoC Voice Spec" voiceLoopType="system" voiceTarget="SoC integration spec" uploadLabel="Upload SoC integration spec" uploadHelper="Used only when no System RTL workflow id is supplied." placeholder="Paste SoC integration spec here..." />
            </div>
          </div>

          {workflowId ? (
            <div className="mt-6 space-y-4">
              <div className="rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                <div className="font-semibold text-slate-100">Run Status</div>
                <div className="mt-2">workflow_id: <span className="break-all text-slate-100">{workflowId}</span></div>
                <div>run_id: <span className="break-all text-slate-100">{runId}</span></div>
                <div>status: <span className="text-slate-100">{workflowRow?.status || "running"}</span></div>
                <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Download ZIP (full=1)</button>
                <div className="mt-4 rounded-xl border border-slate-800 bg-slate-950/70 p-3">
                  <label className="text-xs font-semibold uppercase tracking-wide text-cyan-200">Run next workflow</label>
                  <div className="mt-2 grid gap-2 sm:grid-cols-[1fr_auto]">
                    <select value={nextFlow} onChange={(e) => setNextFlow(e.target.value as typeof nextFlow)} className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-slate-100 outline-none focus:border-cyan-400">
                      <option value="system-synthesis">System Synthesis</option>
                      <option value="system-pd">System PD</option>
                      <option value="system-firmware">System Firmware</option>
                    </select>
                    <button onClick={openNextFlow} className="rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500">Open</button>
                  </div>
                  <div className="mt-2 text-xs text-slate-400">
                    Source System RTL: <span className="break-all text-slate-200">{systemRtlWorkflowId.trim() || workflowId}</span>
                  </div>
                </div>
                <HemChildDashboardLinks logs={workflowRow?.logs} />
              </div>
              <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="dqa" logs={workflowRow?.logs} />
              <AskThisRunPanel workflowId={workflowId} compact />
            </div>
          ) : null}

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((line, index) => <div key={index} className="whitespace-pre-wrap">{line}</div>) : <div className="text-slate-500">No logs yet. Click Run System DQA.</div>}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
