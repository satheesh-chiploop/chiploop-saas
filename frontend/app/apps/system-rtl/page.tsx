"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import VoiceSpecDraft from "@/components/VoiceSpecDraft";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TextFileUpload from "@/components/TextFileUpload";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  SYSTEM_MIXED_SIGNAL_PREFILL_KEY,
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

function systemRtlReady(row: WorkflowRow | null): boolean {
  if (!row) return false;
  const logs = row.logs || "";
  return row.status === "completed" || logs.includes("System App complete: System_RTL") || logs.includes("system_rtl_package.json");
}

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs
    .split("\n")
    .map((l) => l.trimEnd())
    .filter((l) => l.trim().length > 0);
}

export default function SystemRTLAppPage() {
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
  const [digitalSpecText, setDigitalSpecText] = useState("");
  const [analogSpecText, setAnalogSpecText] = useState("");
  const [socIntegrationSpecText, setSocIntegrationSpecText] = useState("");
  const [runSpec2RtlCheck, setRunSpec2RtlCheck] = useState(false);
  const [tempMonitorChain, setTempMonitorChain] = useState(false);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const readyForSystemSim = useMemo(() => systemRtlReady(workflowRow), [workflowRow]);
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
      const {
        data: { session },
      } = await supabase.auth.getSession();

      if (!session?.user) {
        router.replace("/login?next=/apps/system-rtl");
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
    if (!isTempMonitor) return;
    const raw = window.localStorage.getItem(SYSTEM_MIXED_SIGNAL_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as {
        projectName?: string;
        digitalSpecText?: string;
        analogSpecText?: string;
        socIntegrationSpecText?: string;
        runSpec2RtlCheck?: boolean;
      };
      setProjectName(prefill.projectName || "");
      setDigitalSpecText(prefill.digitalSpecText || "");
      setAnalogSpecText(prefill.analogSpecText || "");
      setSocIntegrationSpecText(prefill.socIntegrationSpecText || "");
      setRunSpec2RtlCheck(Boolean(prefill.runSpec2RtlCheck));
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

      if (isActive && !error && data) {
        setWorkflowRow(data as WorkflowRow);
      }
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        {
          event: "*",
          schema: "public",
          table: "workflows",
          filter: `id=eq.${workflowId}`,
        },
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
    if (!digitalSpecText.trim()) return false;
    if (!analogSpecText.trim()) return false;
    if (!socIntegrationSpecText.trim()) return false;
    return true;
  }, [running, digitalSpecText, analogSpecText, socIntegrationSpecText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/rtl/run",
        {
          project_name: projectName || undefined,
          digital_spec_text: digitalSpecText,
          analog_spec_text: analogSpecText,
          soc_integration_spec_text: socIntegrationSpecText,
          toggles: {
            run_spec2rtl_check: runSpec2RtlCheck,
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

  function openSystemSim() {
    if (!workflowId) return;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.demoKind = tempMonitorChain ? "temp_monitor_system" : context.demoKind;
    context.systemRtlWorkflowId = workflowId;
    context.systemRtlRunId = runId || undefined;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    router.push(`/apps/system-sim${tempMonitorChain ? "?tempmon_chain=1" : ""}`);
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
            className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
          >
            Back to Apps
          </button>
          <button
            onClick={() => router.push("/workflow")}
            className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900"
          >
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">System RTL</h1>
          {tempMonitorChain ? (
            <div className="mt-4 rounded-xl border border-emerald-800/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Temperature Monitor System journey: generate digital RTL, analog behavioral collateral, SoC top assembly, SVA, System RTL package, and optional Spec2RTL evidence from the same three-spec source.
            </div>
          ) : null}
          <p className="mt-2 text-slate-300">
            SoC integration + top assembly + RTL handoff artifacts → ZIP.
          </p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input
                value={projectName}
                onChange={(e) => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              />

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-amber-600 hover:bg-amber-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System RTL"}
              </button>
              <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                <input
                  type="checkbox"
                  checked={runSpec2RtlCheck}
                  onChange={(e) => setRunSpec2RtlCheck(e.target.checked)}
                  className="mt-1"
                />
                <span>
                  Run Spec2RTL conformance on generated digital/System RTL evidence
                  <span className="block text-xs text-slate-500">Unchecked by default; enabled for the reference journey.</span>
                </span>
              </label>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

              {workflowId ? (
                <div className="mt-4 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>
                    workflow_id: <span className="text-slate-100">{workflowId}</span>
                  </div>
                  <div>
                    run_id: <span className="text-slate-100">{runId}</span>
                  </div>
                  <button
                    onClick={downloadZip}
                    className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
                  >
                    Download ZIP (full=1)
                  </button>
                  <button
                    type="button"
                    onClick={openSystemSim}
                    disabled={!readyForSystemSim}
                    className="ml-3 mt-3 rounded-xl bg-emerald-600 px-4 py-2 font-semibold text-white hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Open System Sim
                  </button>
                  <div className="mt-4">
                    <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="arch2rtl" logs={workflowRow?.logs} />
                  </div>
                  <AskThisRunPanel workflowId={workflowId} compact />
                </div>
              ) : null}
            </div>

            <div className="space-y-4">
              <div>
                <VoiceSpecDraft title="Digital Voice Spec" loopType="digital" target="System digital spec" compact onApply={setDigitalSpecText} />
                <TextFileUpload
                  compact
                  label="Upload digital spec"
                  helper="Digital RTL/IP behavior, registers, interfaces, interrupts, reset, and clocking."
                  onText={(text, _fileName, mode) => setDigitalSpecText((current) => mergeUploadedText(current, text, mode))}
                />

                <label className="block text-sm text-slate-300">Digital specification *</label>
                <textarea
                  value={digitalSpecText}
                  onChange={(e) => setDigitalSpecText(e.target.value)}
                  rows={6}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                />
              </div>

              <div>
                <VoiceSpecDraft title="Analog Voice Spec" loopType="analog" target="System analog spec" compact onApply={setAnalogSpecText} />
                <TextFileUpload
                  compact
                  label="Upload analog macro spec"
                  helper="Analog is treated as a macro: include abstract behavior, pins, power, timing, LEF/LIB/GDS/SPICE availability, and integration assumptions."
                  onText={(text, _fileName, mode) => setAnalogSpecText((current) => mergeUploadedText(current, text, mode))}
                />

                <label className="block text-sm text-slate-300">Analog specification *</label>
                <textarea
                  value={analogSpecText}
                  onChange={(e) => setAnalogSpecText(e.target.value)}
                  rows={6}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                />
              </div>

              <div>
                <VoiceSpecDraft title="SoC Voice Spec" loopType="system" target="SoC integration spec" compact onApply={setSocIntegrationSpecText} />
                <TextFileUpload
                  compact
                  label="Upload SoC integration spec"
                  helper="Top-level integration, address map, macro hookup, reset/clock/power domains, and verification expectations."
                  onText={(text, _fileName, mode) => setSocIntegrationSpecText((current) => mergeUploadedText(current, text, mode))}
                />

                <label className="block text-sm text-slate-300">SoC integration specification *</label>
                <textarea
                  value={socIntegrationSpecText}
                  onChange={(e) => setSocIntegrationSpecText(e.target.value)}
                  rows={6}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                />
              </div>
            </div>
          </div>

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
                <div className="text-slate-500">No logs yet. Click “Run System RTL”.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}

function mergeUploadedText(current: string, uploaded: string, mode: "append" | "replace") {
  if (mode === "append") return [current.trim(), uploaded.trim()].filter(Boolean).join("\n\n");
  return uploaded;
}
