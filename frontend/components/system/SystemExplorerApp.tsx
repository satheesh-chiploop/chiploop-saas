"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TopNav from "@/components/TopNav";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

const DEMO_GOAL =
  "Explore cache-size tradeoffs for matrix multiplication with gem5 performance results plus power and area analysis; show workload vs cache size charts.";

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

type FormState = {
  project_name: string;
  exploration_type: string;
  workload: string;
  simulator: "gem5";
  isa: string;
  cpu_model: string;
  mode: string;
  cores: number;
  clock: string;
  memory_type: string;
  memory_size: string;
  l1d_size_kb: number[];
  l2_size_kb: number[];
  l1_assoc: number;
  l2_assoc: number;
  cache_line_size: number;
  prefetcher: string;
  branch_predictor: string;
  goal: string;
  isas?: string[];
  cpu_models?: string[];
  memory_types?: string[];
};

type SweepRow = {
  run_id: string;
  workload: string;
  isa: string;
  cpu_model: string;
  cores: number;
  prefetcher: string;
  branch_predictor: string;
  l1d_size_kb: number;
  l2_size_kb: number;
  ipc: number;
  l1d_mpki: number;
  l2_mpki: number;
  estimated_power_w: number;
  estimated_area_mm2: number;
  perf_per_watt: number;
  perf_per_area: number;
  execution_mode?: string;
  sim_insts?: number;
  sim_ticks?: number;
};

const DEFAULT_FORM: FormState = {
  project_name: "matrix_multiply_cache_sweep_demo",
  exploration_type: "cache_tuning",
  workload: "matrix_multiply",
  simulator: "gem5",
  isa: "x86",
  cpu_model: "TimingSimpleCPU",
  mode: "syscall_emulation",
  cores: 1,
  clock: "2GHz",
  memory_type: "DDR3_1600_8x8",
  memory_size: "2GB",
  l1d_size_kb: [16, 32, 64],
  l2_size_kb: [256, 512, 1024],
  l1_assoc: 2,
  l2_assoc: 8,
  cache_line_size: 64,
  prefetcher: "none",
  branch_predictor: "default",
  goal: DEMO_GOAL,
};

type SystemExplorerAppProps = {
  title?: string;
  subtitle?: string;
  defaultForm?: Partial<FormState>;
};

const ISA_OPTIONS = ["x86", "riscv"];
const CPU_OPTIONS = ["TimingSimpleCPU", "MinorCPU", "O3CPU", "AtomicSimpleCPU"];
const MODE_OPTIONS = ["syscall_emulation", "full_system"];
const MEMORY_OPTIONS = ["DDR3_1600_8x8", "DDR4_2400_8x8", "LPDDR5_5500_1x16", "HBM_1000_4H_1x64"];
const PREFETCH_OPTIONS = ["none", "stride", "tagged", "queued"];
const BRANCH_OPTIONS = ["default", "local", "tournament", "bi_mode", "ltage"];
const L1_OPTIONS = [16, 32, 64, 128];
const L2_OPTIONS = [256, 512, 1024, 2048];

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
}

function MultiCheck({ label, options, value, onChange }: { label: string; options: number[]; value: number[]; onChange: (next: number[]) => void }) {
  return (
    <div>
      <div className="text-xs font-semibold text-slate-300">{label}</div>
      <div className="mt-2 grid grid-cols-2 gap-2">
        {options.map((option) => {
          const active = value.includes(option);
          return (
            <button
              key={option}
              type="button"
              onClick={() => {
                const next = active ? value.filter((v) => v !== option) : [...value, option].sort((a, b) => a - b);
                if (next.length) onChange(next);
              }}
              className={`rounded-lg border px-3 py-2 text-sm ${active ? "border-cyan-500 bg-cyan-500/15 text-cyan-100" : "border-slate-800 bg-slate-950 text-slate-300"}`}
            >
              {option}KB
            </button>
          );
        })}
      </div>
    </div>
  );
}

function SelectField({ label, value, options, onChange }: { label: string; value: string; options: string[]; onChange: (value: string) => void }) {
  return (
    <label className="block">
      <span className="text-xs font-semibold text-slate-300">{label}</span>
      <select value={value} onChange={(e) => onChange(e.target.value)} className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100">
        {options.map((option) => <option key={option} value={option}>{option}</option>)}
      </select>
    </label>
  );
}

async function loadGem5ResultRows(workflowId: string): Promise<SweepRow[]> {
  const direct = await fetch(`${API_BASE}/apps/system/architecture/results/${workflowId}`);
  if (direct.ok) {
    const data = await direct.json();
    return Array.isArray(data?.runs) ? data.runs : [];
  }

  const list = await fetch(`${API_BASE}/list_artifacts/${workflowId}`);
  if (!list.ok) {
    const message = direct.status === 404
      ? "gem5 results are not available yet. Confirm the backend was restarted/deployed with the System Architecture results endpoint."
      : `Failed to load gem5 results (${direct.status})`;
    throw new Error(message);
  }
  const artifactIndex = await list.json();
  const relPath = (artifactIndex?.files || []).find((path: string) => path.endsWith("gem5_run_results.json"));
  if (!relPath) {
    throw new Error("gem5_run_results.json was not found in this workflow's artifacts.");
  }
  const artifact = await fetch(`${API_BASE}/download_artifacts/${workflowId}/${encodeURIComponent(relPath).replace(/%2F/g, "/")}`);
  if (!artifact.ok) throw new Error(`Failed to download gem5 results artifact (${artifact.status})`);
  const data = await artifact.json();
  return Array.isArray(data?.runs) ? data.runs : [];
}

function LineChart({ rows, yKey, label, unit = "" }: { rows: SweepRow[]; yKey: keyof SweepRow; label: string; unit?: string }) {
  const width = 560;
  const height = 230;
  const pad = 36;
  const values = rows.map((r) => Number(r[yKey]));
  const minY = Math.min(...values);
  const maxY = Math.max(...values);
  const xVals = Array.from(new Set(rows.map((r) => r.l1d_size_kb))).sort((a, b) => a - b);
  const groups = Array.from(new Set(rows.map((r) => r.l2_size_kb))).sort((a, b) => a - b);
  const palette = ["#22d3ee", "#a78bfa", "#34d399", "#fbbf24"];
  const minX = Math.min(...xVals);
  const maxX = Math.max(...xVals);
  const x = (v: number) => pad + ((v - minX) / Math.max(maxX - minX, 1)) * (width - pad * 2);
  const y = (v: number) => height - pad - ((v - minY) / Math.max(maxY - minY, 0.001)) * (height - pad * 2);

  return (
    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div className="text-sm font-semibold text-slate-100">{label}</div>
        <div className="flex flex-wrap gap-3 text-xs text-slate-400">
          {groups.map((g, index) => <span key={g}><span style={{ color: palette[index % palette.length] }}>●</span> L2 {g}KB</span>)}
        </div>
      </div>
      <svg viewBox={`0 0 ${width} ${height}`} className="mt-3 h-56 w-full">
        <line x1={pad} y1={height - pad} x2={width - pad} y2={height - pad} stroke="#334155" />
        <line x1={pad} y1={pad} x2={pad} y2={height - pad} stroke="#334155" />
        {xVals.map((v) => <text key={v} x={x(v)} y={height - 10} textAnchor="middle" fill="#94a3b8" fontSize="11">{v}KB</text>)}
        <text x={pad} y={24} fill="#94a3b8" fontSize="11">{maxY.toFixed(2)}{unit}</text>
        <text x={pad} y={height - pad - 6} fill="#94a3b8" fontSize="11">{minY.toFixed(2)}{unit}</text>
        {groups.map((g, index) => {
          const groupRows = rows.filter((r) => r.l2_size_kb === g).sort((a, b) => a.l1d_size_kb - b.l1d_size_kb);
          const pts = groupRows.map((r) => `${x(r.l1d_size_kb)},${y(Number(r[yKey]))}`).join(" ");
          const color = palette[index % palette.length];
          return (
            <g key={g}>
              <polyline points={pts} fill="none" stroke={color} strokeWidth="3" />
              {groupRows.map((r) => <circle key={`${g}-${r.l1d_size_kb}`} cx={x(r.l1d_size_kb)} cy={y(Number(r[yKey]))} r="4" fill={color} />)}
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
            <circle cx={x(r.estimated_area_mm2)} cy={y(r.ipc)} r={5 + r.estimated_power_w * 4} fill={r.l1d_size_kb >= 64 ? "#34d399" : r.l1d_size_kb === 32 ? "#a78bfa" : "#22d3ee"} opacity="0.72" />
            <text x={x(r.estimated_area_mm2)} y={y(r.ipc) - 12} textAnchor="middle" fill="#cbd5e1" fontSize="10">{r.l1d_size_kb}/{r.l2_size_kb}</text>
          </g>
        ))}
      </svg>
    </div>
  );
}

export default function SystemExplorerApp({
  title = "System Architecture Explorer",
  subtitle = "No-code gem5 exploration. Configure architecture knobs, run, then inspect PPA charts from that run.",
  defaultForm,
}: SystemExplorerAppProps) {
  const router = useRouter();
  const initialForm = useMemo<FormState>(() => ({ ...DEFAULT_FORM, ...(defaultForm || {}) }), [defaultForm]);
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [trialPrompt, setTrialPrompt] = useState<TrialPrompt | null>(null);
  const [form, setForm] = useState<FormState>(initialForm);
  const [resultRows, setResultRows] = useState<SweepRow[] | null>(null);
  const [resultError, setResultError] = useState<string | null>(null);
  const logsRef = useRef<HTMLDivElement | null>(null);
  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const completed = workflowRow?.status === "completed";
  const failed = workflowRow?.status === "failed";
  const recommended = useMemo(() => resultRows ? [...resultRows].sort((a, b) => b.perf_per_watt - a.perf_per_watt)[0] : null, [resultRows]);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  useEffect(() => {
    if (!completed || !workflowId || resultRows) return;
    let active = true;
    (async () => {
      setResultError(null);
      try {
        const rows = await loadGem5ResultRows(workflowId);
        if (!rows.length) throw new Error("gem5 completed but no run rows were found in gem5_run_results.json");
        if (active) setResultRows(rows);
      } catch (e: any) {
        if (active) setResultError(e?.message || String(e));
      }
    })();
    return () => {
      active = false;
    };
  }, [completed, workflowId, resultRows]);

  useEffect(() => {
    setForm(initialForm);
  }, [initialForm]);

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

  function payloadFromForm(current: FormState) {
    return {
      project_name: current.project_name,
      exploration_type: current.exploration_type,
      workload: current.workload,
      simulator: current.simulator,
      isa: current.isa,
      cpu_model: current.cpu_model,
      mode: current.mode,
      cores: current.cores,
      clock: current.clock,
      memory_type: current.memory_type,
      memory_size: current.memory_size,
      l1_assoc: current.l1_assoc,
      l2_assoc: current.l2_assoc,
      cache_line_size: current.cache_line_size,
      prefetcher: current.prefetcher,
      branch_predictor: current.branch_predictor,
      isas: current.isas,
      cpu_models: current.cpu_models,
      memory_types: current.memory_types,
      goal: current.goal,
      sweep: { l1d_size_kb: current.l1d_size_kb, l2_size_kb: current.l2_size_kb },
      toggles: { enable_power_estimation: true, enable_area_estimation: true, enable_visualizations: true },
    };
  }

  async function runExplorer() {
    setErr(null);
    setTrialPrompt(null);
    setRunning(true);
    setWorkflowRow(null);
    setWorkflowId(null);
    setRunId(null);
    setResultRows(null);
    setResultError(null);
    try {
      const resp = await fetch(`${API_BASE}/apps/system/architecture/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(payloadFromForm(form)),
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
            <h1 className="mt-1 text-3xl font-bold">{title}</h1>
            <p className="mt-2 max-w-3xl text-slate-300">{subtitle}</p>
          </div>
          <div className="flex gap-2">
            <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Apps</button>
            <button onClick={() => router.push("/workflow")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Studio</button>
          </div>
        </div>

        <section className="mt-6 grid gap-5 lg:grid-cols-[410px_1fr]">
          <aside className="space-y-4">
            <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
              <div className="flex items-center justify-between gap-3">
                <div>
                  <div className="text-sm font-semibold text-slate-100">Startup demo</div>
                  <div className="mt-1 text-xs text-slate-400">Prefilled matrix multiply cache sweep.</div>
                </div>
                <button onClick={() => setForm(initialForm)} className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-800">Reset</button>
              </div>

              <div className="mt-5 grid gap-4">
                <SelectField label="ISA" value={form.isa} options={ISA_OPTIONS} onChange={(isa) => setForm({ ...form, isa })} />
                <SelectField label="CPU model" value={form.cpu_model} options={CPU_OPTIONS} onChange={(cpu_model) => setForm({ ...form, cpu_model })} />
                <SelectField label="Mode" value={form.mode} options={MODE_OPTIONS} onChange={(mode) => setForm({ ...form, mode })} />
                <div className="grid grid-cols-2 gap-3">
                  <label className="block">
                    <span className="text-xs font-semibold text-slate-300">Cores</span>
                    <input type="number" min={1} max={8} value={form.cores} onChange={(e) => setForm({ ...form, cores: Math.max(1, Number(e.target.value) || 1) })} className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100" />
                  </label>
                  <label className="block">
                    <span className="text-xs font-semibold text-slate-300">Clock</span>
                    <input value={form.clock} onChange={(e) => setForm({ ...form, clock: e.target.value })} className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100" />
                  </label>
                </div>
                <SelectField label="Memory" value={form.memory_type} options={MEMORY_OPTIONS} onChange={(memory_type) => setForm({ ...form, memory_type })} />
                <div className="grid grid-cols-2 gap-3">
                  <SelectField label="Prefetcher" value={form.prefetcher} options={PREFETCH_OPTIONS} onChange={(prefetcher) => setForm({ ...form, prefetcher })} />
                  <SelectField
                    label="Branch predictor"
                    value={form.branch_predictor}
                    options={BRANCH_OPTIONS}
                    onChange={(branch_predictor) => setForm({
                      ...form,
                      branch_predictor,
                      cpu_model: branch_predictor !== "default" && ["TimingSimpleCPU", "AtomicSimpleCPU"].includes(form.cpu_model) ? "O3CPU" : form.cpu_model,
                    })}
                  />
                </div>
                <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-1">
                  <MultiCheck label="L1D sweep" options={L1_OPTIONS} value={form.l1d_size_kb} onChange={(l1d_size_kb) => setForm({ ...form, l1d_size_kb })} />
                  <MultiCheck label="L2 sweep" options={L2_OPTIONS} value={form.l2_size_kb} onChange={(l2_size_kb) => setForm({ ...form, l2_size_kb })} />
                </div>
              </div>

              <button onClick={runExplorer} disabled={running} className="mt-5 w-full rounded-lg bg-cyan-600 px-4 py-3 font-semibold hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700">
                {running ? "Starting..." : workflowId ? "Run Again With Settings" : "Run Demo"}
              </button>
              {err ? <div className="mt-3 rounded-lg border border-red-900/60 bg-red-950/30 p-3 text-sm text-red-200">{err}</div> : null}
              {trialPrompt ? (
                <div className="mt-3 rounded-lg border border-cyan-900/60 bg-cyan-950/30 p-3 text-sm text-cyan-100">
                  <div>{trialPrompt.message}</div>
                  {typeof trialPrompt.runsRemaining === "number" ? <div className="mt-1 text-cyan-200">Demo runs remaining: {trialPrompt.runsRemaining}</div> : null}
                  {trialPrompt.checkoutUrl ? <button onClick={() => router.push(trialPrompt.checkoutUrl || "/pricing?trial=1")} className="mt-3 rounded-lg bg-cyan-600 px-3 py-2 font-semibold hover:bg-cyan-500">{trialPrompt.checkoutLabel || "Start trial"}</button> : null}
                </div>
              ) : null}
            </div>

            {recommended ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
                <div className="text-sm font-semibold text-slate-100">Run recommendation</div>
                <div className="mt-3 text-2xl font-bold text-emerald-300">{recommended.l1d_size_kb}KB L1D / {recommended.l2_size_kb}KB L2</div>
                <div className="mt-2 text-sm text-slate-300">Best balance for gem5 IPC, activity-based power, and configured area in this run.</div>
                <div className="mt-4 grid grid-cols-2 gap-2 text-sm">
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">IPC</div><div className="text-lg font-semibold">{recommended.ipc}</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Power</div><div className="text-lg font-semibold">{recommended.estimated_power_w}W</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Area</div><div className="text-lg font-semibold">{recommended.estimated_area_mm2}</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Perf/W</div><div className="text-lg font-semibold">{recommended.perf_per_watt}</div></div>
                </div>
              </div>
            ) : null}

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
            {!workflowId ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-8">
                <div className="text-lg font-semibold text-slate-100">Ready to run</div>
                <p className="mt-2 max-w-2xl text-sm leading-6 text-slate-300">
                  The demo is prefilled like Arch2RTL. Click Run Demo, wait for the System workflow to finish, and the PPA charts will appear here. Change ISA, CPU, cores, memory, prefetcher, or cache sweep and run again to compare behavior.
                </p>
              </div>
            ) : failed ? (
              <div className="rounded-lg border border-red-900/60 bg-red-950/30 p-8">
                <div className="text-lg font-semibold text-red-100">gem5 run failed</div>
                <p className="mt-2 text-sm text-red-200">Charts are only generated from real gem5 results. Check the run log for the missing tool, unsupported option, or workload setup error.</p>
              </div>
            ) : !completed || !resultRows ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-8">
                <div className="text-lg font-semibold text-slate-100">Running System Architecture Explorer</div>
                <p className="mt-2 text-sm text-slate-300">Charts will appear after gem5 finishes and ChipLoop parses stats.txt.</p>
                {resultError ? <div className="mt-3 rounded-lg border border-red-900/60 bg-red-950/30 p-3 text-sm text-red-200">{resultError}</div> : null}
              </div>
            ) : (
              <>
                <div className="grid gap-5 xl:grid-cols-2">
                  <LineChart rows={resultRows} yKey="ipc" label="Workload vs cache size: IPC" />
                  <LineChart rows={resultRows} yKey="l1d_mpki" label="Workload vs cache size: L1D MPKI" />
                </div>
                <BubbleChart rows={resultRows} />
                <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
                  <div className="mb-3 text-sm font-semibold text-slate-100">Sweep table</div>
                  <div className="overflow-x-auto">
                    <table className="w-full min-w-[900px] text-left text-sm">
                      <thead className="text-slate-400">
                        <tr>
                          <th className="py-2">Workload</th>
                          <th>ISA</th>
                          <th>CPU</th>
                          <th>Cores</th>
                          <th>Prefetch</th>
                          <th>Branch</th>
                          <th>L1D</th>
                          <th>L2</th>
                          <th>IPC</th>
                          <th>L1D MPKI</th>
                          <th>L2 MPKI</th>
                          <th>Power</th>
                          <th>Area</th>
                          <th>Mode</th>
                        </tr>
                      </thead>
                      <tbody>
                        {resultRows.map((r) => (
                          <tr key={r.run_id} className="border-t border-slate-800 text-slate-200">
                            <td className="py-2">{r.workload}</td>
                            <td>{r.isa}</td>
                            <td>{r.cpu_model}</td>
                            <td>{r.cores}</td>
                            <td>{r.prefetcher}</td>
                            <td>{r.branch_predictor}</td>
                            <td>{r.l1d_size_kb}KB</td>
                            <td>{r.l2_size_kb}KB</td>
                            <td>{r.ipc}</td>
                            <td>{r.l1d_mpki}</td>
                            <td>{r.l2_mpki}</td>
                            <td>{r.estimated_power_w}W</td>
                            <td>{r.estimated_area_mm2}</td>
                            <td>{r.execution_mode || "gem5"}</td>
                          </tr>
                        ))}
                      </tbody>
                    </table>
                  </div>
                </div>
              </>
            )}

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
