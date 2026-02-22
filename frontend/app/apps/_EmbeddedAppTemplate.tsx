"use client";

import { useEffect, useMemo, useState } from "react";
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

type Props = {
  title: string;
  subtitle: string;
  runPath: string; // e.g. "/apps/embedded/hal/run"
};

export default function EmbeddedAppTemplate({ title, subtitle, runPath }: Props) {
  const router = useRouter();

  const [loading, setLoading] = useState(true);
  const [userId, setUserId] = useState<string | null>(null);

  const [specText, setSpecText] = useState("");
  const [goal, setGoal] = useState("");

  const [toolchain, setToolchain] = useState<Record<string, string>>({
    fw_language: "rust",
    fw_build: "cargo",
    rtl_sim: "verilator",
    tb_framework: "cocotb",
    coverage_fw: "llvm-cov",
    coverage_rtl: "verilator_cov",
  });

  const [toggles, setToggles] = useState<Record<string, boolean>>({
    enable_cosim: true,
    enable_coverage: true,
  });

  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  function authHeaders(): Record<string, string> {
    // If you’re using cookie auth, you may not need anything here.
    // Kept minimal like your DQA page pattern.
    return {};
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
      const { data } = await supabase.auth.getUser();
      const uid = data?.user?.id ?? null;
      setUserId(uid);
      setLoading(false);
      if (!uid) router.push("/");
    })();
  }, [router]);

  // Subscribe to workflow row (same as DQA)
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
    return specText.trim().length > 0;
  }, [running, specText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(runPath, {
        spec_text: specText,
        goal: goal || undefined,
        toolchain,
        toggles,
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

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loading…</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      {/* Top bar (same vibe as DQA/Apps) */}
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button
            className="flex items-center gap-2 text-xl font-extrabold"
            onClick={() => router.push("/apps")}
            title="Apps Home"
          >
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">{title}</span>
          </button>

          <div className="flex items-center gap-3">
            <button
              className="rounded-lg border border-slate-700 bg-slate-900/40 px-3 py-2 text-sm hover:bg-slate-800"
              onClick={() => router.push("/workflow")}
            >
              Studio
            </button>
            <button
              className="rounded-lg border border-slate-700 bg-slate-900/40 px-3 py-2 text-sm hover:bg-slate-800"
              onClick={async () => {
                await supabase.auth.signOut();
                router.push("/");
              }}
            >
              Logout
            </button>
          </div>
        </div>
      </div>

      <div className="mx-auto max-w-6xl px-6 py-8 space-y-6">
        <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-6">
          <div className="text-2xl font-extrabold">{title}</div>
          <div className="mt-1 text-slate-300">{subtitle}</div>
        </div>

        {/* One-shot intake */}
        <div className="grid grid-cols-1 gap-6 lg:grid-cols-2">
          <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-6 space-y-4">
            <div className="text-lg font-bold">One-shot input</div>

            <label className="block text-sm text-slate-300">Spec / context</label>
            <textarea
              value={specText}
              onChange={(e) => setSpecText(e.target.value)}
              className="h-48 w-full rounded-xl border border-slate-800 bg-black/40 p-3 text-sm outline-none focus:border-cyan-600"
              placeholder="Paste spec excerpt, register map notes, requirements, constraints..."
            />

            <label className="block text-sm text-slate-300">Goal (optional)</label>
            <input
              value={goal}
              onChange={(e) => setGoal(e.target.value)}
              className="w-full rounded-xl border border-slate-800 bg-black/40 p-3 text-sm outline-none focus:border-cyan-600"
              placeholder="What should this app deliver?"
            />

            {err ? <div className="text-sm text-red-400">{err}</div> : null}

            <div className="flex items-center gap-3 pt-2">
              <button
                disabled={!canRun}
                onClick={runNow}
                className={`rounded-xl px-4 py-2 text-sm font-semibold ${
                  canRun ? "bg-cyan-700 hover:bg-cyan-600" : "bg-slate-800 text-slate-400 cursor-not-allowed"
                }`}
              >
                {running ? "Running…" : "Run"}
              </button>

              <button
                disabled={!workflowId}
                onClick={downloadZip}
                className={`rounded-xl px-4 py-2 text-sm font-semibold border border-slate-700 ${
                  workflowId ? "hover:bg-slate-900" : "text-slate-500 cursor-not-allowed"
                }`}
              >
                Download ZIP
              </button>
            </div>

            {workflowId ? (
              <div className="text-xs text-slate-400">
                workflow: <span className="text-slate-200">{workflowId}</span>
                {runId ? (
                  <>
                    {" "}
                    · run: <span className="text-slate-200">{runId}</span>
                  </>
                ) : null}
              </div>
            ) : null}
          </div>

          {/* Toolchain + toggles */}
          <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-6 space-y-4">
            <div className="text-lg font-bold">Toolchain</div>

            {Object.entries(toolchain).map(([k, v]) => (
              <div key={k} className="flex items-center gap-3">
                <div className="w-40 text-sm text-slate-300">{k}</div>
                <input
                  value={v}
                  onChange={(e) => setToolchain((prev) => ({ ...prev, [k]: e.target.value }))}
                  className="flex-1 rounded-xl border border-slate-800 bg-black/40 p-2 text-sm outline-none focus:border-cyan-600"
                />
              </div>
            ))}

            <div className="pt-2 text-lg font-bold">Toggles</div>
            {Object.entries(toggles).map(([k, v]) => (
              <label key={k} className="flex items-center gap-3 text-sm text-slate-300">
                <input
                  type="checkbox"
                  checked={!!v}
                  onChange={(e) => setToggles((prev) => ({ ...prev, [k]: e.target.checked }))}
                />
                {k}
              </label>
            ))}
          </div>
        </div>

        {/* Live logs */}
        <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-6">
          <div className="flex items-center justify-between">
            <div className="text-lg font-bold">Live logs</div>
            <div className="text-sm text-slate-300">
              phase: <span className="text-slate-100">{workflowRow?.phase || "—"}</span>{" "}
              · status: <span className="text-slate-100">{workflowRow?.status || "—"}</span>
            </div>
          </div>

          <pre className="mt-4 max-h-[420px] overflow-auto whitespace-pre-wrap rounded-xl border border-slate-800 bg-black/40 p-4 text-xs text-slate-200">
            {workflowRow?.logs || "Run to see logs here…"}
          </pre>
        </div>
      </div>
    </main>
  );
}