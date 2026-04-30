"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { apiPost } from "@/lib/apiClient";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";
const ONBOARDING_DEMO_KEY = "chiploop_arch2rtl_onboarding_demo";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map(l => l.trimEnd()).filter(l => l.trim().length > 0);
}

export default function Arch2RTLAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [guidedOnboarding, setGuidedOnboarding] = useState(false);
  const [onboardingCompleted, setOnboardingCompleted] = useState(false);

  // Intake
  const [projectName, setProjectName] = useState("");
  const [topModule, setTopModule] = useState("");
  const [designLanguage, setDesignLanguage] = useState<"systemverilog" | "verilog">("systemverilog");
  const [specText, setSpecText] = useState("");

  const [genRegmap, setGenRegmap] = useState(true);
  const [genUpfLite, setGenUpfLite] = useState(false);
  const [genPackaging, setGenPackaging] = useState(true);

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

  async function postJSON<T>(path: string, body: unknown): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...authHeaders() },
      body: JSON.stringify(body),
    });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` â€” ${txt}` : ""}`);
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
        router.replace("/login?next=/apps/arch2rtl");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const guided = new URLSearchParams(window.location.search).get("guided") === "1";
    if (!guided) return;

    setGuidedOnboarding(true);
    const raw = window.localStorage.getItem(ONBOARDING_DEMO_KEY);
    if (!raw) return;

    try {
      const demo = JSON.parse(raw) as {
        projectName?: string;
        topModule?: string;
        designLanguage?: "systemverilog" | "verilog";
        specText?: string;
        toggles?: { genRegmap?: boolean; genUpfLite?: boolean; genPackaging?: boolean };
      };
      setProjectName(demo.projectName || "pwm_controller_onboarding");
      setTopModule(demo.topModule || "pwm_controller");
      setDesignLanguage(demo.designLanguage || "systemverilog");
      setSpecText(demo.specText || "");
      setGenRegmap(demo.toggles?.genRegmap ?? true);
      setGenUpfLite(demo.toggles?.genUpfLite ?? true);
      setGenPackaging(demo.toggles?.genPackaging ?? true);
    } catch {
      window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
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

      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
        (payload) => {
          const row = payload.new as Partial<WorkflowRow>;
          setWorkflowRow({
            id: row.id || workflowId,
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
    if (!specText.trim()) return false;
    if (!topModule.trim()) return false;
    return true;
  }, [running, specText, topModule]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/arch2rtl/run",
        {
          project_name: projectName || undefined,
          top_module: topModule,
          design_language: designLanguage,
          spec_text: specText,
          toggles: {
            gen_regmap: genRegmap,
            gen_upf_lite: genUpfLite,
            gen_packaging: genPackaging,
          },
        }
      );
      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
      if (guidedOnboarding) {
        apiPost("/settings/onboarding", {
          action: "start",
          last_step: "arch2rtl_workflow_started",
          workflow_id: out.workflow_id,
          metadata: { demo: "arch2rtl" },
        }).catch(() => undefined);
      }
    } catch (e: unknown) {
      setErr(e instanceof Error ? e.message : String(e));
    } finally {
      setRunning(false);
    }
  }

  async function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
    if (guidedOnboarding) {
      try {
        await apiPost("/settings/onboarding", {
          action: "complete",
          workflow_id: workflowId,
          last_step: "downloaded_artifacts",
          metadata: { demo: "arch2rtl", reviewed_files: ["rtl/*.sv", "constraints/*.sdc", "power/*.upf"] },
        });
        setOnboardingCompleted(true);
        window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
      } catch {
        setOnboardingCompleted(true);
      }
    }
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loadingâ€¦</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-6xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
            â† Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">
            Studio
          </button>
        </div>

        {guidedOnboarding ? (
          <div className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/20 p-5">
            <div className="flex flex-wrap items-start justify-between gap-4">
              <div>
                <div className="text-sm font-semibold uppercase tracking-wide text-cyan-300">Guided first activity</div>
                <h2 className="mt-1 text-2xl font-bold text-white">Run Arch2RTL and inspect the handoff package</h2>
                <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                  The PWM controller spec is already filled in. Click Run Arch2RTL, wait for logs to finish, then download the ZIP and inspect the RTL, SDC, and UPF files.
                </p>
              </div>
              {onboardingCompleted ? (
                <span className="rounded-full border border-emerald-700 bg-emerald-950/40 px-3 py-1 text-sm text-emerald-100">
                  Completed
                </span>
              ) : null}
            </div>
            <div className="mt-4 grid gap-3 md:grid-cols-4">
              {[
                "Review pre-filled PWM spec",
                "Run Arch2RTL",
                "Open the downloaded RTL, SDC, and UPF files",
                "Download ZIP to complete onboarding",
              ].map((item, idx) => (
                <div key={item} className="rounded-xl border border-slate-800 bg-black/25 p-3 text-sm text-slate-200">
                  <div className="mb-2 flex h-7 w-7 items-center justify-center rounded-full bg-cyan-600 text-xs font-bold">{idx + 1}</div>
                  {item}
                </div>
              ))}
            </div>
          </div>
        ) : null}

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Arch2RTL</h1>
          <p className="mt-2 text-slate-300">One-shot intake â†’ one click run â†’ progressive outputs â†’ ZIP handoff.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input value={projectName} onChange={e => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Top module *</label>
              <input value={topModule} onChange={e => setTopModule(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Design language</label>
              <select value={designLanguage} onChange={e => setDesignLanguage(e.target.value as "systemverilog" | "verilog")}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                <option value="systemverilog">SystemVerilog</option>
                <option value="verilog">Verilog</option>
              </select>

              <div className="mt-3 space-y-2">
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genRegmap} onChange={e => setGenRegmap(e.target.checked)} />
                  Generate regmap
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genUpfLite} onChange={e => setGenUpfLite(e.target.checked)} />
                  Generate UPF-lite
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genPackaging} onChange={e => setGenPackaging(e.target.checked)} />
                  Generate packaging/handoff
                </label>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Startingâ€¦" : "Run Arch2RTL"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

              {workflowId ? (
                <div className="mt-4 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>workflow_id: <span className="text-slate-100">{workflowId}</span></div>
                  <div>run_id: <span className="text-slate-100">{runId}</span></div>
                  <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                    {guidedOnboarding ? "Download ZIP and finish" : "Download ZIP (full=1)"}
                  </button>
                </div>
              ) : null}
            </div>

            <div>
              <label className="block text-sm text-slate-300">Spec text *</label>
              <textarea
                value={specText}
                onChange={e => setSpecText(e.target.value)}
                rows={18}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste your spec hereâ€¦"
              />
              <div className="mt-2 text-xs text-slate-500">Tip: keep it structured (interfaces, clocks, resets, targets).</div>
            </div>
          </div>

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((l, i) => <div key={i} className="whitespace-pre-wrap">{l}</div>) : (
                <div className="text-slate-500">No logs yet. Click â€œRun Arch2RTLâ€.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}




