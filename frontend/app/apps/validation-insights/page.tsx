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

export default function ValidationInsightsPage() {
  const router = useRouter();

  const [loading, setLoading] = useState(true);
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [email, setEmail] = useState<string | null>(null);

  const [lookbackRuns, setLookbackRuns] = useState(10);
  const [tagsText, setTagsText] = useState("");
  const [enableEvolution, setEnableEvolution] = useState(true);
  const [enableCoverage, setEnableCoverage] = useState(true);

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

  const tags = useMemo(() => {
    const t = tagsText.split(",").map((s) => s.trim()).filter(Boolean);
    return t.length ? t : undefined;
  }, [tagsText]);

  const canRun = useMemo(() => Number.isFinite(lookbackRuns) && lookbackRuns > 0, [lookbackRuns]);

  async function runApp() {
    setRunErr(null);
    setRunning(true);
    setWorkflowId(null);
    setRunId(null);
    setWorkflowRow(null);

    try {
      const body = {
        lookback_runs: lookbackRuns,
        tags,
        enable_evolution: enableEvolution,
        enable_coverage: enableCoverage,
      };

      const res = await postJSON<{ ok?: boolean; workflow_id: string; run_id?: string }>(
        "/apps/validation-insights/run",
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
          <h1 className="text-xl font-semibold">Validation Insights</h1>
          <div className="text-sm text-neutral-500">Analyze historical runs → detect patterns → evolve plan.</div>
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
        <div className="grid grid-cols-1 md:grid-cols-2 gap-3">
          <div>
            <div className="text-sm font-medium">Lookback runs</div>
            <input
              type="number"
              min={1}
              className="mt-1 w-full rounded border p-2 text-sm"
              value={lookbackRuns}
              onChange={(e) => setLookbackRuns(parseInt(e.target.value || "10", 10))}
            />
          </div>

          <div>
            <div className="text-sm font-medium">Tags (optional, comma-separated)</div>
            <input
              className="mt-1 w-full rounded border p-2 text-sm"
              value={tagsText}
              onChange={(e) => setTagsText(e.target.value)}
              placeholder="e.g., dnss, bringup, v1"
            />
          </div>
        </div>

        <div className="flex flex-wrap gap-4 text-sm">
          <label className="flex items-center gap-2">
            <input type="checkbox" checked={enableEvolution} onChange={(e) => setEnableEvolution(e.target.checked)} />
            Enable evolution
          </label>

          <label className="flex items-center gap-2">
            <input type="checkbox" checked={enableCoverage} onChange={(e) => setEnableCoverage(e.target.checked)} />
            Enable coverage proposal
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