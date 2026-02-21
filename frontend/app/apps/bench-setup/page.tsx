"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";

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

export default function BenchSetupAppPage() {
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
  const [benchName, setBenchName] = useState("");
  const [instrumentsJson, setInstrumentsJson] = useState(
    JSON.stringify(
      [
        { name: "DMM_1", type: "DMM", address: "USB::0x1234::0x5678::INSTR" },
        { name: "PSU_1", type: "PSU", address: "TCPIP::192.168.0.10::INSTR" },
      ],
      null,
      2
    )
  );
  const [enableSchematic, setEnableSchematic] = useState(true);
  const [enablePreflight, setEnablePreflight] = useState(false);

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

      const {
        data: { session },
      } = await supabase.auth.getSession();

      if (!session?.user) {
        router.replace("/login?next=/apps/bench-setup");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

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
    if (!benchName.trim()) return false;
    // instruments JSON should parse
    try {
      const parsed = JSON.parse(instrumentsJson || "[]");
      if (!Array.isArray(parsed)) return false;
    } catch {
      return false;
    }
    return true;
  }, [running, benchName, instrumentsJson]);

  async function runNow() {
    setErr(null);
    setRunning(true);

    let instruments: any[] = [];
    try {
      instruments = JSON.parse(instrumentsJson || "[]");
      if (!Array.isArray(instruments)) throw new Error("Instrument list must be a JSON array.");
    } catch (e: any) {
      setErr(e?.message || "Invalid instruments JSON.");
      setRunning(false);
      return;
    }

    try {
      const out = await postJSON<{ ok?: boolean; workflow_id: string; run_id?: string }>(
        "/apps/bench-setup/run",
        {
          bench_name: benchName.trim(),
          instruments,
          enable_schematic: enableSchematic,
          enable_preflight: enablePreflight,
        }
      );

      setWorkflowId(out.workflow_id);
      setRunId(out.run_id || null);
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
            className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 transition"
          >
            ← Back to Apps
          </button>
          <button
            onClick={() => router.push("/workflow")}
            className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900 transition"
          >
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Validation Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Bench Setup</h1>
          <p className="mt-2 text-slate-300">
            Register instruments → create bench → schematic → optional preflight.
          </p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            {/* Left: Form */}
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Bench name *</label>
              <input
                value={benchName}
                onChange={(e) => setBenchName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="e.g., DNSS Bench A"
              />

              <label className="block text-sm text-slate-300">Instrument list (JSON array) *</label>
              <textarea
                value={instrumentsJson}
                onChange={(e) => setInstrumentsJson(e.target.value)}
                rows={10}
                className="w-full rounded-2xl border border-slate-800 bg-black/30 p-4 font-mono text-xs text-slate-100"
                placeholder='[{"name":"DMM_1","type":"DMM","address":"USB::..."}]'
              />

              <div className="flex items-center gap-6 text-sm text-slate-300">
                <label className="flex items-center gap-2">
                  <input
                    type="checkbox"
                    checked={enableSchematic}
                    onChange={(e) => setEnableSchematic(e.target.checked)}
                  />
                  Enable schematic
                </label>

                <label className="flex items-center gap-2">
                  <input
                    type="checkbox"
                    checked={enablePreflight}
                    onChange={(e) => setEnablePreflight(e.target.checked)}
                  />
                  Enable preflight
                </label>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run Bench Setup"}
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

            {/* Right: Helpful panel */}
            <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
              <div className="text-sm font-semibold text-slate-100">Outputs</div>
              <ul className="mt-3 space-y-2 text-sm text-slate-300">
                <li>• validation/bench_setup.json</li>
                <li>• validation/bench_schematic.png or .json (optional)</li>
                <li>• validation/preflight_summary.md (optional)</li>
              </ul>

              <div className="mt-6 text-sm font-semibold text-slate-100">Notes</div>
              <div className="mt-2 text-sm text-slate-300">
                Use stable instrument names (DMM_1, PSU_1). Addresses can be VISA USB/TCPIP strings or your lab abstraction.
              </div>

              <div className="mt-4 text-xs text-slate-500">
                Tip: keep the JSON array small and clean for now. We can add preset dropdowns later.
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
                <div className="text-slate-500">No logs yet. Click “Run Bench Setup”.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}