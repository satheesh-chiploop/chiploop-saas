"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TopNav from "@/components/TopNav";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

const DEMO_PAYLOAD = {
  project_name: "matrix_multiply_cache_sweep_demo",
  workload: "matrix_multiply",
  simulator: "gem5",
  isa: "x86",
  cpu_model: "TimingSimpleCPU",
  mode: "syscall_emulation",
  goal:
    "Explore cache-size tradeoffs for matrix multiplication with performance, power, and area estimates; show workload vs cache size charts.",
  sweep: {
    l1d_size_kb: [16, 32, 64],
    l2_size_kb: [256, 512, 1024],
  },
  toggles: {
    enable_power_estimation: true,
    enable_area_estimation: true,
    enable_visualizations: true,
  },
};

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type TrialPrompt = {
  message: string;
  checkoutUrl?: string;
  checkoutLabel?: string;
  runsRemaining?: number;
};

type SweepRow = {
  run_id: string;
  workload: string;
  l1d_size_kb: number;
  l2_size_kb: number;
  ipc: number;
  l1d_mpki: number;
  l2_mpki: number;
  estimated_power_w: number;
  estimated_area_mm2: number;
  perf_per_watt: number;
  perf_per_area: number;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
}

function estimate(l1: number, l2: number) {
  const l1Gain = l1 === 16 ? 0 : l1 === 32 ? 0.16 : 0.22;
  const l2Gain = l2 === 256 ? 0 : l2 === 512 ? 0.1 : 0.14;
  const ipc = Number((0.82 + l1Gain + l2Gain).toFixed(3));
  const l1d_mpki = Number(Math.max(18, 44 - l1 / 2.7).toFixed(2));
  const l2_mpki = Number(Math.max(6.5, 19 - l2 / 92).toFixed(2));
  const estimated_power_w = Number((1.05 + l1 * 0.006 + l2 * 0.00055).toFixed(3));
  const estimated_area_mm2 = Number((0.3 + l1 * 0.0032 + l2 * 0.00042).toFixed(3));
  return {
    ipc,
    l1d_mpki,
    l2_mpki,
    estimated_power_w,
    estimated_area_mm2,
    perf_per_watt: Number((ipc / estimated_power_w).toFixed(3)),
    perf_per_area: Number((ipc / estimated_area_mm2).toFixed(3)),
  };
}

function demoRows(): SweepRow[] {
  const rows: SweepRow[] = [];
  let idx = 1;
  for (const l1 of DEMO_PAYLOAD.sweep.l1d_size_kb) {
    for (const l2 of DEMO_PAYLOAD.sweep.l2_size_kb) {
      rows.push({
        run_id: `archsim_${String(idx).padStart(2, "0")}`,
        workload: DEMO_PAYLOAD.workload,
        l1d_size_kb: l1,
        l2_size_kb: l2,
        ...estimate(l1, l2),
      });
      idx += 1;
    }
  }
  return rows;
}

function LineChart({ rows, yKey, label, unit = "" }: { rows: SweepRow[]; yKey: keyof SweepRow; label: string; unit?: string }) {
  const width = 560;
  const height = 230;
  const pad = 36;
  const values = rows.map((r) => Number(r[yKey]));
  const minY = Math.min(...values);
  const maxY = Math.max(...values);
  const xVals = [16, 32, 64];
  const groups = [256, 512, 1024];
  const colors: Record<number, string> = { 256: "#22d3ee", 512: "#a78bfa", 1024: "#34d399" };
  const x = (v: number) => pad + ((v - 16) / 48) * (width - pad * 2);
  const y = (v: number) => height - pad - ((v - minY) / Math.max(maxY - minY, 0.001)) * (height - pad * 2);

  return (
    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
      <div className="flex items-center justify-between gap-3">
        <div className="text-sm font-semibold text-slate-100">{label}</div>
        <div className="flex gap-3 text-xs text-slate-400">
          {groups.map((g) => <span key={g}><span style={{ color: colors[g] }}>●</span> L2 {g}KB</span>)}
        </div>
      </div>
      <svg viewBox={`0 0 ${width} ${height}`} className="mt-3 h-56 w-full">
        <line x1={pad} y1={height - pad} x2={width - pad} y2={height - pad} stroke="#334155" />
        <line x1={pad} y1={pad} x2={pad} y2={height - pad} stroke="#334155" />
        {xVals.map((v) => (
          <text key={v} x={x(v)} y={height - 10} textAnchor="middle" fill="#94a3b8" fontSize="11">{v}KB</text>
        ))}
        <text x={pad} y={24} fill="#94a3b8" fontSize="11">{maxY.toFixed(2)}{unit}</text>
        <text x={pad} y={height - pad - 6} fill="#94a3b8" fontSize="11">{minY.toFixed(2)}{unit}</text>
        {groups.map((g) => {
          const pts = rows.filter((r) => r.l2_size_kb === g).map((r) => `${x(r.l1d_size_kb)},${y(Number(r[yKey]))}`).join(" ");
          return (
            <g key={g}>
              <polyline points={pts} fill="none" stroke={colors[g]} strokeWidth="3" />
              {rows.filter((r) => r.l2_size_kb === g).map((r) => (
                <circle key={`${g}-${r.l1d_size_kb}`} cx={x(r.l1d_size_kb)} cy={y(Number(r[yKey]))} r="4" fill={colors[g]} />
              ))}
            </g>
          );
        })}
      </svg>
    </div>
  );
}

function BubbleChart({ rows }: { rows: SweepRow[] }) {
  const width = 560;
  const height = 230;
  const pad = 36;
  const minX = Math.min(...rows.map((r) => r.estimated_area_mm2));
  const maxX = Math.max(...rows.map((r) => r.estimated_area_mm2));
  const minY = Math.min(...rows.map((r) => r.ipc));
  const maxY = Math.max(...rows.map((r) => r.ipc));
  const x = (v: number) => pad + ((v - minX) / Math.max(maxX - minX, 0.001)) * (width - pad * 2);
  const y = (v: number) => height - pad - ((v - minY) / Math.max(maxY - minY, 0.001)) * (height - pad * 2);
  return (
    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
      <div className="text-sm font-semibold text-slate-100">PPA Bubble: area vs IPC, bubble size = power</div>
      <svg viewBox={`0 0 ${width} ${height}`} className="mt-3 h-56 w-full">
        <line x1={pad} y1={height - pad} x2={width - pad} y2={height - pad} stroke="#334155" />
        <line x1={pad} y1={pad} x2={pad} y2={height - pad} stroke="#334155" />
        <text x={width / 2} y={height - 8} textAnchor="middle" fill="#94a3b8" fontSize="11">estimated area mm2</text>
        <text x={pad} y={24} fill="#94a3b8" fontSize="11">IPC</text>
        {rows.map((r) => (
          <g key={r.run_id}>
            <circle
              cx={x(r.estimated_area_mm2)}
              cy={y(r.ipc)}
              r={5 + r.estimated_power_w * 4}
              fill={r.l1d_size_kb === 64 ? "#34d399" : r.l1d_size_kb === 32 ? "#a78bfa" : "#22d3ee"}
              opacity="0.72"
            />
            <text x={x(r.estimated_area_mm2)} y={y(r.ipc) - 12} textAnchor="middle" fill="#cbd5e1" fontSize="10">
              {r.l1d_size_kb}/{r.l2_size_kb}
            </text>
          </g>
        ))}
      </svg>
    </div>
  );
}

export default function SystemArchitecturePage() {
  const router = useRouter();
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [trialPrompt, setTrialPrompt] = useState<TrialPrompt | null>(null);
  const logsRef = useRef<HTMLDivElement | null>(null);
  const rows = useMemo(() => demoRows(), []);
  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const recommended = useMemo(() => [...rows].sort((a, b) => b.perf_per_watt - a.perf_per_watt)[0], [rows]);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  useEffect(() => {
    (async () => {
      setLoading(true);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/system-architecture");
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
      const { data, error } = await supabase.from("workflows").select("id,status,phase,logs,updated_at").eq("id", workflowId).single();
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

  function authHeaders(): HeadersInit {
    const h: Record<string, string> = {};
    if (sessionUserId) h["x-user-id"] = sessionUserId;
    if (accessToken) h["Authorization"] = `Bearer ${accessToken}`;
    return h;
  }

  async function runDemo() {
    setErr(null);
    setTrialPrompt(null);
    setRunning(true);
    try {
      const resp = await fetch(`${API_BASE}/apps/system/architecture/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(DEMO_PAYLOAD),
      });
      const text = await resp.text();
      const data = text ? JSON.parse(text) : {};
      if (!resp.ok) {
        const detail = data?.detail ?? data;
        if (detail?.requires_checkout) {
          setTrialPrompt({
            message: detail.message || "Start your 7-day trial to run custom architecture exploration.",
            checkoutUrl: detail.checkout_url || "/pricing?trial=1",
            checkoutLabel: detail.checkout_label || "Start 7-day trial",
          });
        }
        throw new Error(typeof detail === "string" ? detail : detail?.message || `${resp.status} ${resp.statusText}`);
      }
      setWorkflowId(data.workflow_id);
      setRunId(data.run_id);
      if (data.trial_cta?.show) {
        setTrialPrompt({
          message: data.trial_cta.message,
          checkoutUrl: data.trial_cta.checkout_url,
          checkoutLabel: data.trial_cta.checkout_label,
          runsRemaining: data.demo?.runs_remaining,
        });
      }
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
    return <main className="flex min-h-screen items-center justify-center bg-slate-950 text-slate-200">Loading...</main>;
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="apps" showPlanBadge maxWidthClass="max-w-7xl" />
      <div className="mx-auto max-w-7xl px-4 py-8 sm:px-6">
        <div className="flex flex-wrap items-center justify-between gap-3">
          <div>
            <div className="text-sm font-medium text-cyan-200">System Loop</div>
            <h1 className="mt-1 text-3xl font-bold">System Architecture Explorer</h1>
            <p className="mt-2 max-w-3xl text-slate-300">
              No-code gem5 exploration for workload, cache-size, performance, power, and area tradeoffs.
            </p>
          </div>
          <div className="flex gap-2">
            <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Apps</button>
            <button onClick={() => router.push("/workflow")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Studio</button>
          </div>
        </div>

        <section className="mt-6 grid gap-5 lg:grid-cols-[360px_1fr]">
          <aside className="space-y-4">
            <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
              <div className="text-sm font-semibold text-slate-100">Prebuilt demo</div>
              <div className="mt-3 space-y-3 text-sm text-slate-300">
                <div className="flex justify-between"><span>Tool</span><span className="text-cyan-200">gem5</span></div>
                <div className="flex justify-between"><span>Workload</span><span>matrix_multiply</span></div>
                <div className="flex justify-between"><span>CPU</span><span>TimingSimpleCPU</span></div>
                <div className="flex justify-between"><span>Sweep</span><span>L1D/L2 cache</span></div>
                <div className="flex justify-between"><span>Output</span><span>PPA charts</span></div>
              </div>
              <button
                onClick={runDemo}
                disabled={running}
                className="mt-5 w-full rounded-lg bg-cyan-600 px-4 py-3 font-semibold hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
              >
                {running ? "Starting..." : "Run Demo"}
              </button>
              {err ? <div className="mt-3 rounded-lg border border-red-900/60 bg-red-950/30 p-3 text-sm text-red-200">{err}</div> : null}
              {trialPrompt ? (
                <div className="mt-3 rounded-lg border border-cyan-900/60 bg-cyan-950/30 p-3 text-sm text-cyan-100">
                  <div>{trialPrompt.message}</div>
                  {typeof trialPrompt.runsRemaining === "number" ? <div className="mt-1 text-cyan-200">Demo runs remaining: {trialPrompt.runsRemaining}</div> : null}
                  {trialPrompt.checkoutUrl ? (
                    <button onClick={() => router.push(trialPrompt.checkoutUrl || "/pricing?trial=1")} className="mt-3 rounded-lg bg-cyan-600 px-3 py-2 font-semibold hover:bg-cyan-500">
                      {trialPrompt.checkoutLabel || "Start trial"}
                    </button>
                  ) : null}
                </div>
              ) : null}
            </div>

            <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
              <div className="text-sm font-semibold text-slate-100">Recommendation</div>
              <div className="mt-3 text-2xl font-bold text-emerald-300">{recommended.l1d_size_kb}KB L1D / {recommended.l2_size_kb}KB L2</div>
              <div className="mt-2 text-sm text-slate-300">Best demo balance for performance per watt and performance per area.</div>
              <div className="mt-4 grid grid-cols-2 gap-2 text-sm">
                <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">IPC</div><div className="text-lg font-semibold">{recommended.ipc}</div></div>
                <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Power</div><div className="text-lg font-semibold">{recommended.estimated_power_w}W</div></div>
                <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Area</div><div className="text-lg font-semibold">{recommended.estimated_area_mm2}</div></div>
                <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Perf/W</div><div className="text-lg font-semibold">{recommended.perf_per_watt}</div></div>
              </div>
            </div>

            {workflowId ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5 text-sm text-slate-300">
                <div>workflow_id: <span className="text-slate-100">{workflowId}</span></div>
                <div>run_id: <span className="text-slate-100">{runId}</span></div>
                <div className="mt-2">status: <span className="text-cyan-200">{workflowRow?.status || "queued"}</span></div>
                <div className="mt-3 flex flex-wrap gap-2">
                  <button onClick={downloadZip} className="rounded-lg border border-slate-700 px-3 py-2 text-slate-100 hover:bg-slate-800">Download ZIP</button>
                </div>
                <div className="mt-3"><AskThisRunPanel workflowId={workflowId} compact /></div>
              </div>
            ) : null}
          </aside>

          <section className="space-y-5">
            <div className="grid gap-5 xl:grid-cols-2">
              <LineChart rows={rows} yKey="ipc" label="Workload vs cache size: IPC" />
              <LineChart rows={rows} yKey="l1d_mpki" label="Workload vs cache size: L1D MPKI" />
            </div>
            <BubbleChart rows={rows} />
            <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
              <div className="mb-3 text-sm font-semibold text-slate-100">Sweep table</div>
              <div className="overflow-x-auto">
                <table className="w-full min-w-[780px] text-left text-sm">
                  <thead className="text-slate-400">
                    <tr>
                      <th className="py-2">Workload</th>
                      <th>L1D</th>
                      <th>L2</th>
                      <th>IPC</th>
                      <th>L1D MPKI</th>
                      <th>L2 MPKI</th>
                      <th>Power</th>
                      <th>Area</th>
                    </tr>
                  </thead>
                  <tbody>
                    {rows.map((r) => (
                      <tr key={r.run_id} className="border-t border-slate-800 text-slate-200">
                        <td className="py-2">{r.workload}</td>
                        <td>{r.l1d_size_kb}KB</td>
                        <td>{r.l2_size_kb}KB</td>
                        <td>{r.ipc}</td>
                        <td>{r.l1d_mpki}</td>
                        <td>{r.l2_mpki}</td>
                        <td>{r.estimated_power_w}W</td>
                        <td>{r.estimated_area_mm2}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>

            {workflowId ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                <div className="mb-2 text-sm font-semibold text-slate-200">Run log</div>
                <div ref={logsRef} className="max-h-72 overflow-auto rounded-lg bg-slate-950 p-3 font-mono text-xs text-slate-300">
                  {logLines.length ? logLines.map((line, i) => <div key={i}>{line}</div>) : <div>Waiting for workflow logs...</div>}
                </div>
              </div>
            ) : null}
          </section>
        </section>
      </div>
    </main>
  );
}
