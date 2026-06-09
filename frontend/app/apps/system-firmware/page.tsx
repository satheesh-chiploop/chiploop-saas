"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import SpecTextBox from "@/components/SpecTextBox";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  SOFTWARE_HANDOFF_PREFILL_KEY,
  SYSTEM_MIXED_SIGNAL_PREFILL_KEY,
  TEMP_MONITOR_SYSTEM_FIRMWARE_SPEC,
  TEMP_MONITOR_SYSTEM_SOFTWARE_GOAL,
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
type SystemRtlSourceMode = "from_system_rtl" | "paste" | "repo_path";

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
}

function systemFirmwareReady(row: WorkflowRow | null): boolean {
  if (!row) return false;
  const logs = row.logs || "";
  return row.status === "completed" || logs.includes("System App complete: System_Firmware") || logs.includes("system_software_handoff");
}

export default function SystemFirmwareAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  // Intake
  const [projectName, setProjectName] = useState("");

  const [digitalSpecText, setDigitalSpecText] = useState("");
  const [analogSpecText, setAnalogSpecText] = useState("");
  const [socIntegrationSpecText, setSocIntegrationSpecText] = useState("");
  const [rtlSourceMode, setRtlSourceMode] = useState<SystemRtlSourceMode>("from_system_rtl");
  const [repoPath, setRepoPath] = useState("");
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");
  const [tempMonitorChain, setTempMonitorChain] = useState(false);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const readyForSoftware = useMemo(() => systemFirmwareReady(workflowRow), [workflowRow]);
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
        router.replace("/login?next=/apps/system-firmware");
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
      };
      setProjectName(prefill.projectName ? `${prefill.projectName}_firmware` : "");
      setDigitalSpecText(`${prefill.digitalSpecText || ""}\n\nFirmware intent:\n${TEMP_MONITOR_SYSTEM_FIRMWARE_SPEC}`);
      setAnalogSpecText(prefill.analogSpecText || "");
      setSocIntegrationSpecText(prefill.socIntegrationSpecText || "");
    } catch {
      window.localStorage.removeItem(SYSTEM_MIXED_SIGNAL_PREFILL_KEY);
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

  const canRun = useMemo(() => {
    if (running) return false;
    if (rtlSourceMode === "from_system_rtl" && !systemRtlWorkflowId.trim()) return false;
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "paste" && ![digitalSpecText, analogSpecText, socIntegrationSpecText].some((text) => text.trim())) return false;
    return true;
  }, [running, rtlSourceMode, systemRtlWorkflowId, repoPath, digitalSpecText, analogSpecText, socIntegrationSpecText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/firmware/run",
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

  function openSystemSoftware() {
    if (!workflowId) return;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.demoKind = tempMonitorChain ? "temp_monitor_system" : context.demoKind;
    if (systemRtlWorkflowId.trim()) context.systemRtlWorkflowId = systemRtlWorkflowId.trim();
    context.systemFirmwareWorkflowId = workflowId;
    context.systemFirmwareRunId = runId || undefined;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    window.localStorage.setItem(SOFTWARE_HANDOFF_PREFILL_KEY, JSON.stringify({
      projectName: "temp_monitor_system_software",
      systemFirmwareWorkflowId: workflowId,
      systemRtlWorkflowId: context.systemRtlWorkflowId || "",
      softwareGoal: TEMP_MONITOR_SYSTEM_SOFTWARE_GOAL,
      appNames: "tempmon_cli, tempmon_service",
      targetLanguage: "rust",
      sdkStyle: "rust_crate",
      buildSystem: "cargo",
      notes: "System-first mixed-signal temperature monitor reference journey.",
    }));
    router.push(`/apps/system-software?handoff=1${tempMonitorChain ? "&tempmon_chain=1" : ""}`);
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
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">System Firmware</h1>
          {tempMonitorChain ? (
            <div className="mt-4 rounded-xl border border-emerald-800/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Temperature Monitor System journey: generate firmware from the System RTL/register handoff, then pass the real firmware package into System Software.
            </div>
          ) : null}
          <p className="mt-2 text-slate-300">Register extract → driver scaffold → build → co-sim → ZIP.</p>

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

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-amber-600 hover:bg-amber-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System Firmware"}
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
                    onClick={openSystemSoftware}
                    disabled={!readyForSoftware}
                    className="ml-3 mt-3 rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Open System Software
                  </button>
                  <div className="mt-4">
                    <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="embedded" logs={workflowRow?.logs} />
                  </div>
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
                    uploadHelper="Digital Verilog/SystemVerilog register/control logic used for firmware handoff."
                  />
                  <SpecTextBox
                    label="Analog RTL / behavioral model"
                    value={analogSpecText}
                    onChange={setAnalogSpecText}
                    voiceTitle="Analog Model Voice Input"
                    voiceLoopType="analog"
                    voiceTarget="System analog RTL or behavioral model"
                    uploadLabel="Upload analog model"
                    uploadHelper="Analog macro pins, behavior, status/observation points, and firmware-visible assumptions."
                  />
                  <SpecTextBox
                    label="SoC RTL"
                    value={socIntegrationSpecText}
                    onChange={setSocIntegrationSpecText}
                    voiceTitle="SoC RTL Voice Input"
                    voiceLoopType="system"
                    voiceTarget="SoC RTL"
                    uploadLabel="Upload SoC RTL"
                    uploadHelper="Address map, macro hookup, firmware-visible registers, interrupts, and integration constraints."
                  />
                </>
              ) : (
                <div className="rounded-2xl border border-slate-800 bg-black/20 p-4 text-sm text-slate-300">
                  {rtlSourceMode === "from_system_rtl"
                    ? "Using the selected System RTL workflow as the firmware RTL/register source."
                    : "Using RTL from the repo/path as the firmware RTL/register source."}
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
                  onClick={openSystemSoftware}
                  disabled={!readyForSoftware}
                  className="rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                >
                  Open System Software
                </button>
              </div>
              <div className="mt-4">
                <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="embedded" logs={workflowRow?.logs} />
              </div>
              <div className="mt-4">
                <AskThisRunPanel workflowId={workflowId} compact />
              </div>
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
                <div className="text-slate-500">No logs yet. Click “Run System Firmware”.</div>
              )}
            </div>
          </div>

        </div>
      </div>
    </main>
  );
}
