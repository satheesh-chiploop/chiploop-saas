"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import VoiceSpecDraft from "@/components/VoiceSpecDraft";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

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

export default function SystemSoftwareAppPage() {
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
  const [systemSoftwareHandoffPath, setSystemSoftwareHandoffPath] = useState(
    "system/software_handoff/system_software_handoff.json"
  );
  const [systemFirmwareWorkflowId, setSystemFirmwareWorkflowId] = useState("");
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");
  const [softwareGoal, setSoftwareGoal] = useState("");
  const [appNamesText, setAppNamesText] = useState("");
  const [targetLanguage, setTargetLanguage] = useState("mixed");
  const [sdkStyle, setSdkStyle] = useState("mixed");
  const [buildSystem, setBuildSystem] = useState("cmake");
  const [notes, setNotes] = useState("");
  const [useHandoffPath, setUseHandoffPath] = useState(true);

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

  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/system-software");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (!workflowId) return;

    let isActive = true;

    (async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .single();

      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
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

  const appNames = useMemo(() => {
    return appNamesText
      .split(",")
      .map((x) => x.trim())
      .filter(Boolean);
  }, [appNamesText]);

  const canRun = useMemo(() => {
    if (running) return false;
    if (useHandoffPath) return !!systemSoftwareHandoffPath.trim();
    return !!systemFirmwareWorkflowId.trim();
  }, [running, useHandoffPath, systemSoftwareHandoffPath, systemFirmwareWorkflowId]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/software/run",
        {
          project_name: projectName || undefined,
          system_software_handoff_path: useHandoffPath ? systemSoftwareHandoffPath || undefined : undefined,
          system_firmware_workflow_id: !useHandoffPath ? systemFirmwareWorkflowId || undefined : undefined,
          system_rtl_workflow_id: systemRtlWorkflowId || undefined,
          software_goal: softwareGoal || undefined,
          app_names: appNames.length ? appNames : undefined,
          target_language: targetLanguage || undefined,
          sdk_style: sdkStyle || undefined,
          build_system: buildSystem || undefined,
          notes: notes || undefined,
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
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">System Software</h1>
          <p className="mt-2 text-slate-300">
            Handoff ingest → capability model → API contract → SDK scaffold.
          </p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input
                value={projectName}
                onChange={(e) => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              />

              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-200">Primary input mode</div>
                <div className="mt-3 flex gap-4">
                  <label className="flex items-center gap-2 text-sm text-slate-300">
                    <input
                      type="radio"
                      checked={useHandoffPath}
                      onChange={() => setUseHandoffPath(true)}
                    />
                    Use handoff path
                  </label>
                  <label className="flex items-center gap-2 text-sm text-slate-300">
                    <input
                      type="radio"
                      checked={!useHandoffPath}
                      onChange={() => setUseHandoffPath(false)}
                    />
                    Use firmware workflow id
                  </label>
                </div>

                {useHandoffPath ? (
                  <div className="mt-3">
                    <label className="block text-sm text-slate-300">System software handoff path *</label>
                    <input
                      value={systemSoftwareHandoffPath}
                      onChange={(e) => setSystemSoftwareHandoffPath(e.target.value)}
                      className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                      placeholder="system/software_handoff/system_software_handoff.json"
                    />
                  </div>
                ) : (
                  <div className="mt-3">
                    <label className="block text-sm text-slate-300">
                      System firmware workflow id *
                    </label>
                    <input
                      value={systemFirmwareWorkflowId}
                      onChange={(e) => setSystemFirmwareWorkflowId(e.target.value)}
                      className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                      placeholder="Optional future reuse hook"
                    />
                  </div>
                )}

                <div className="mt-3">
                  <label className="block text-sm text-slate-300">
                    System RTL workflow id (optional)
                  </label>
                  <input
                    value={systemRtlWorkflowId}
                    onChange={(e) => setSystemRtlWorkflowId(e.target.value)}
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="Optional future reuse hook"
                  />
                </div>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System Software"}
              </button>

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
                </div>
              ) : null}
            </div>

            <div className="space-y-4">
              <div>
                <VoiceSpecDraft title="Software Voice Spec" loopType="software" target="System Software spec" compact onApply={setSoftwareGoal} />

                <label className="block text-sm text-slate-300">Software goal</label>
                <textarea
                  value={softwareGoal}
                  onChange={(e) => setSoftwareGoal(e.target.value)}
                  rows={4}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Describe the software package you want to build..."
                />
              </div>

              <div>
                <label className="block text-sm text-slate-300">
                  Application names (comma-separated)
                </label>
                <input
                  value={appNamesText}
                  onChange={(e) => setAppNamesText(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="health_app, diag_cli, telemetry_agent"
                />
              </div>

              <div className="grid gap-4 md:grid-cols-3">
                <div>
                  <label className="block text-sm text-slate-300">Target language</label>
                  <select
                    value={targetLanguage}
                    onChange={(e) => setTargetLanguage(e.target.value)}
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="c">C</option>
                    <option value="rust">Rust</option>
                    <option value="mixed">Mixed</option>
                  </select>
                </div>

                <div>
                  <label className="block text-sm text-slate-300">SDK style</label>
                  <select
                    value={sdkStyle}
                    onChange={(e) => setSdkStyle(e.target.value)}
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="c_sdk">C SDK</option>
                    <option value="rust_crate">Rust crate</option>
                    <option value="mixed">Mixed</option>
                  </select>
                </div>

                <div>
                  <label className="block text-sm text-slate-300">Build system</label>
                  <select
                    value={buildSystem}
                    onChange={(e) => setBuildSystem(e.target.value)}
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="cmake">CMake</option>
                    <option value="cargo">Cargo</option>
                    <option value="make">Make</option>
                  </select>
                </div>
              </div>

              <div>
                <label className="block text-sm text-slate-300">Notes (optional)</label>
                <textarea
                  value={notes}
                  onChange={(e) => setNotes(e.target.value)}
                  rows={5}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Additional software packaging or API notes..."
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
                <div className="text-slate-500">No logs yet. Click “Run System Software”.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
