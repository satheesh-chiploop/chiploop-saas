"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

type WorkflowRowLite = {
  id: string;
  status: string | null;
  phase: string | null;
  logs: string | null;
  updated_at?: string | null;
};

export default function BenchSetupPage() {
  const router = useRouter();

  const [loading, setLoading] = useState(true);
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [email, setEmail] = useState<string | null>(null);

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

  const [running, setRunning] = useState(false);
  const [runErr, setRunErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRowLite | null>(null);

  function authHeaders(userId?: string, token?: string): HeadersInit {
    const h: Record<string, string> = {};
    const uid = userId ?? sessionUserId;
    const tok = token ?? accessToken;
    if (uid) h["x-user-id"] = uid;
    if (tok) h["Authorization"] = `Bearer ${tok}`;
    return h;
  }

  async function postJSON<T>(path: string, body: any, headersOverride?: HeadersInit): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...(headersOverride ?? authHeaders()) },
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
      const { data: { session } } = await supabase.auth.getSession();
      if (!session) {
        router.push("/login");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setEmail(session.user.email || null);
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

      if (!isActive) return;
      if (!error && data) {
        setWorkflowRow({
          id: data.id,
          status: data.status,
          phase: data.phase,
          logs: data.logs,
          updated_at: data.updated_at,
        });
      }
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

  const canRun = useMemo(() => benchName.trim().length >= 3, [benchName]);

  async function runApp() {
    setRunErr(null);
    setRunning(true);
    setWorkflowId(null);
    setRunId(null);
    setWorkflowRow(null);

    let instruments: any[] = [];
    try {
      instruments = JSON.parse(instrumentsJson || "[]");
      if (!Array.isArray(instruments)) throw new Error("Instruments JSON must be an array");
    } catch (e: any) {
      setRunErr(e?.message || "Invalid instruments JSON");
      setRunning(false);
      return;
    }

    try {
      const body = {
        bench_name: benchName.trim(),
        instruments,
        enable_schematic: enableSchematic,
        enable_preflight: enablePreflight,
      };

      const res = await postJSON<{ ok?: boolean; workflow_id: string; run_id?: string }>(
        "/apps/bench-setup/run",
        body
      );

      setWorkflowId(res.workflow_id);
      setRunId(res.run_id ?? null);
    } catch (e: any) {
      setRunErr(e?.message || String(e));
    } finally {
      setRunning(false);
    }
  }

  function downloadZip(full = true) {
    if (!workflowId) return;
    const url = `${API_BASE}/workflow/${workflowId}/download_zip${full ? "?full=1" : ""}`;
    window.open(url, "_blank");
  }

  const phase = workflowRow?.phase ?? "—";
  const status = workflowRow?.status ?? "—";
  const logs = workflowRow?.logs ?? "";

  if (loading) return <div className="p-4 text-sm text-neutral-500">Loading…</div>;

  return (
    <div className="p-4 space-y-4">
      <div className="flex items-start justify-between gap-4">
        <div>
          <div className="text-xs text-neutral-500">Signed in: {email ?? sessionUserId}</div>
          <h1 className="text-xl font-semibold">Bench Setup</h1>
          <div className="text-sm text-neutral-500">
            Register instruments → create bench → schematic → optional preflight.
          </div>
        </div>
        <div className="text-right text-xs text-neutral-500">
          <div>Phase: {phase}</div>
          <div>Status: {status}</div>
        </div>
      </div>

      {runErr ? (
        <div className="rounded border border-red-300 bg-red-50 p-3 text-sm text-red-700">{runErr}</div>
      ) : null}

      <div className="rounded border p-4 space-y-3">
        <div>
          <div className="text-sm font-medium">Bench name</div>
          <input
            className="mt-1 w-full rounded border p-2 text-sm"
            value={benchName}
            onChange={(e) => setBenchName(e.target.value)}
            placeholder="e.g., DNSS Bench A"
          />
        </div>

        <div>
          <div className="text-sm font-medium">Instrument list (JSON array)</div>
          <textarea
            className="mt-1 w-full rounded border p-2 text-sm min-h-[160px] font-mono"
            value={instrumentsJson}
            onChange={(e) => setInstrumentsJson(e.target.value)}
          />
        </div>

        <div className="flex flex-wrap gap-4 text-sm">
          <label className="flex items-center gap-2">
            <input type="checkbox" checked={enableSchematic} onChange={(e) => setEnableSchematic(e.target.checked)} />
            Enable schematic
          </label>
          <label className="flex items-center gap-2">
            <input type="checkbox" checked={enablePreflight} onChange={(e) => setEnablePreflight(e.target.checked)} />
            Enable preflight
          </label>
        </div>

        <div className="flex items-center gap-2">
          <button
            onClick={runApp}
            disabled={!canRun || running}
            className="rounded bg-cyan-700 hover:bg-cyan-600 disabled:opacity-50 px-3 py-2 text-sm text-white"
          >
            {running ? "Running…" : "Run"}
          </button>

          <button
            onClick={() => downloadZip(true)}
            disabled={!workflowId}
            className="rounded border px-3 py-2 text-sm hover:bg-neutral-50 disabled:opacity-50"
          >
            Download ZIP
          </button>

          {workflowId ? <div className="text-xs text-neutral-500">workflow: {workflowId}</div> : null}
          {runId ? <div className="text-xs text-neutral-500">run: {runId}</div> : null}
        </div>
      </div>

      <div className="rounded border p-4">
        <div className="flex items-center justify-between mb-2">
          <div className="text-sm font-medium">Live logs</div>
          <div className="text-xs text-neutral-500">{workflowRow?.updated_at ? `updated: ${workflowRow.updated_at}` : ""}</div>
        </div>
        <pre className="text-xs whitespace-pre-wrap max-h-[520px] overflow-auto">
          {logs?.trim() ? logs : "No logs yet."}
        </pre>
      </div>
    </div>
  );
}