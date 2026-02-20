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

export default function VerifyAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  // Intake (minimal but useful)
  const [rtlSourceMode, setRtlSourceMode] = useState<"from_arch2rtl" | "paste" | "repo_path">("repo_path");
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [repoPath, setRepoPath] = useState("");
  const [pastedRtl, setPastedRtl] = useState("");

  const [testIntent, setTestIntent] = useState("");
  const [randomVsDirected, setRandomVsDirected] = useState<"random" | "directed">("random");
  const [coverageTargets, setCoverageTargets] = useState("");
  const [simulatorType, setSimulatorType] = useState("");
  const [seedCount, setSeedCount] = useState<number>(10);

  const [enableFormal, setEnableFormal] = useState(false);
  const [enableGoldenModel, setEnableGoldenModel] = useState(false);

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

      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/verify");
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

    // need rtl source and test intent
    if (!testIntent.trim()) return false;
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "from_arch2rtl" && !fromWorkflowId.trim()) return false;
    if (rtlSourceMode === "paste" && !pastedRtl.trim()) return false;

    // seed_count sanity
    if (!Number.isFinite(seedCount) || seedCount <= 0) return false;

    return true;
  }, [running, testIntent, rtlSourceMode, repoPath, fromWorkflowId, pastedRtl, seedCount]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/verify/run",
        {
          rtl_source_mode: rtlSourceMode,
          from_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
          repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
          pasted_rtl_files:
            rtlSourceMode === "paste"
              ? [{ path: "rtl/top.sv", content: pastedRtl }]
              : undefined,

          test_intent: testIntent,
          random_vs_directed: randomVsDirected,
          coverage_targets: coverageTargets || undefined,
          simulator_type: simulatorType || undefined,
          seed_count: seedCount,

          toggles: {
            enable_formal: enableFormal,
            enable_golden_model: enableGoldenModel,
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
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Verify</h1>
          <p className="mt-2 text-slate-300">
            Verification Intelligence: TB + SVA + Coverage plan + Simulation summary (optional formal/golden model).
          </p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">RTL source</label>
              <select
                value={rtlSourceMode}
                onChange={(e) => setRtlSourceMode(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="repo_path">Repo / path</option>
                <option value="from_arch2rtl">Use Arch2RTL output</option>
                <option value="paste">Paste RTL</option>
              </select>

              {rtlSourceMode === "repo_path" ? (
                <>
                  <label className="block text-sm text-slate-300">Repo path *</label>
                  <input
                    value={repoPath}
                    onChange={(e) => setRepoPath(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="/path/to/repo or git URL"
                  />
                </>
              ) : null}

              {rtlSourceMode === "from_arch2rtl" ? (
                <>
                  <label className="block text-sm text-slate-300">From workflow_id *</label>
                  <input
                    value={fromWorkflowId}
                    onChange={(e) => setFromWorkflowId(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="workflow_id from Arch2RTL"
                  />
                </>
              ) : null}

              <label className="block text-sm text-slate-300">Test intent *</label>
              <textarea
                value={testIntent}
                onChange={(e) => setTestIntent(e.target.value)}
                rows={6}
                className="w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="What should the testbench verify? Any scenarios, reset behavior, corner cases…"
              />

              <div className="grid grid-cols-2 gap-3">
                <div>
                  <label className="block text-sm text-slate-300">Random vs directed</label>
                  <select
                    value={randomVsDirected}
                    onChange={(e) => setRandomVsDirected(e.target.value as any)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="random">Random</option>
                    <option value="directed">Directed</option>
                  </select>
                </div>

                <div>
                  <label className="block text-sm text-slate-300">Seed count</label>
                  <input
                    type="number"
                    min={1}
                    value={seedCount}
                    onChange={(e) => setSeedCount(parseInt(e.target.value || "10", 10))}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  />
                </div>
              </div>

              <label className="block text-sm text-slate-300">Coverage targets (optional)</label>
              <input
                value={coverageTargets}
                onChange={(e) => setCoverageTargets(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="e.g., 90% line, 80% functional"
              />

              <label className="block text-sm text-slate-300">Simulator (optional)</label>
              <input
                value={simulatorType}
                onChange={(e) => setSimulatorType(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="e.g., iverilog / verilator / vcs / xcelium"
              />

              <div className="mt-2 space-y-2">
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input
                    type="checkbox"
                    checked={enableFormal}
                    onChange={(e) => setEnableFormal(e.target.checked)}
                  />
                  Enable formal (optional)
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input
                    type="checkbox"
                    checked={enableGoldenModel}
                    onChange={(e) => setEnableGoldenModel(e.target.checked)}
                  />
                  Enable golden model comparison (optional)
                </label>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run Verify"}
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

            <div>
              <label className="block text-sm text-slate-300">Paste RTL (only if RTL source = paste)</label>
              <textarea
                value={pastedRtl}
                onChange={(e) => setPastedRtl(e.target.value)}
                rows={18}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste your RTL here… (minimal mode stores it as rtl/top.sv)"
                disabled={rtlSourceMode !== "paste"}
              />
              <div className="mt-2 text-xs text-slate-500">
                Minimal mode: saved as one file. We can enhance later to multi-file paste.
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
                <div className="text-slate-500">No logs yet. Click “Run Verify”.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
