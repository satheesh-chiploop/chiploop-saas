"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TopNav from "@/components/TopNav";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const ARCH2RTL_HANDOFF_KEY = "chiploop_arch2rtl_handoff_prefill";

type SweepRow = {
  run_id: string;
  workload?: string;
  isa?: string;
  cpu_model?: string;
  cores?: number;
  l1d_size_kb?: number;
  l2_size_kb?: number;
  prefetcher?: string;
  branch_predictor?: string;
  ipc?: number;
  l1d_mpki?: number;
  l2_mpki?: number;
  estimated_power_w?: number;
  estimated_area_mm2?: number;
  perf_per_watt?: number;
  perf_per_area?: number;
};

type Arch2RtlPrefill = {
  projectName: string;
  topModule: string;
  designLanguage: "systemverilog" | "verilog";
  specText: string;
  toggles: { genRegmap: boolean; genUpfLite: boolean; genPackaging: boolean };
};

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
};

type TrialCta = {
  message: string;
  checkoutUrl: string;
  checkoutLabel: string;
};

async function loadGem5Rows(workflowId: string): Promise<SweepRow[]> {
  const direct = await fetch(`${API_BASE}/apps/system/architecture/results/${workflowId}`);
  if (direct.ok) {
    const data = await direct.json();
    return Array.isArray(data?.runs) ? data.runs : [];
  }
  const list = await fetch(`${API_BASE}/list_artifacts/${workflowId}`);
  if (!list.ok) throw new Error(`Could not find System Architecture results for ${workflowId}`);
  const artifactIndex = await list.json();
  const relPath = (artifactIndex?.files || []).find((path: string) => path.endsWith("gem5_run_results.json"));
  if (!relPath) throw new Error("gem5_run_results.json was not found for this workflow.");
  const artifact = await fetch(`${API_BASE}/download_artifacts/${workflowId}/${encodeURIComponent(relPath).replace(/%2F/g, "/")}`);
  if (!artifact.ok) throw new Error(`Failed to download gem5 results artifact (${artifact.status})`);
  const data = await artifact.json();
  return Array.isArray(data?.runs) ? data.runs : [];
}

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter((line) => line.trim().length > 0);
}

function errorMessage(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

export default function ArchitectureToRtlDeliveryPage() {
  const router = useRouter();
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [workflowId, setWorkflowId] = useState("");
  const [rows, setRows] = useState<SweepRow[]>([]);
  const [selectedRunId, setSelectedRunId] = useState("");
  const [prefill, setPrefill] = useState<Arch2RtlPrefill | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [arch2rtlWorkflowId, setArch2rtlWorkflowId] = useState<string | null>(null);
  const [busy, setBusy] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [runError, setRunError] = useState<string | null>(null);
  const [runNotice, setRunNotice] = useState<string | null>(null);
  const [trialCta, setTrialCta] = useState<TrialCta | null>(null);

  const recommended = useMemo(() => {
    if (!rows.length) return null;
    return [...rows].sort((a, b) =>
      ((b.perf_per_watt || 0) - (a.perf_per_watt || 0)) ||
      ((b.perf_per_area || 0) - (a.perf_per_area || 0)) ||
      ((b.ipc || 0) - (a.ipc || 0))
    )[0];
  }, [rows]);

  const selected = useMemo(() => rows.find((row) => row.run_id === selectedRunId) || recommended, [recommended, rows, selectedRunId]);
  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);

  useEffect(() => {
    (async () => {
      setLoading(true);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/architecture-to-rtl");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      const params = new URLSearchParams(window.location.search);
      const wf = params.get("workflow_id") || "";
      const run = params.get("run_id") || "";
      if (wf) setWorkflowId(wf);
      if (run) setSelectedRunId(run);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (!arch2rtlWorkflowId) return;
    let isActive = true;
    (async () => {
      const { data, error } = await supabase.from("workflows").select("id,status,phase,logs").eq("id", arch2rtlWorkflowId).single();
      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
    })();
    const channel = supabase
      .channel(`arch2rtl-delivery-${arch2rtlWorkflowId}`)
      .on("postgres_changes", { event: "*", schema: "public", table: "workflows", filter: `id=eq.${arch2rtlWorkflowId}` }, (payload) => {
        const row = payload.new as Partial<WorkflowRow>;
        setWorkflowRow({ id: row.id || arch2rtlWorkflowId, status: row.status, phase: row.phase, logs: row.logs });
      })
      .subscribe();
    return () => {
      isActive = false;
      supabase.removeChannel(channel);
    };
  }, [arch2rtlWorkflowId]);

  function authHeaders(): HeadersInit {
    const headers: Record<string, string> = {};
    if (sessionUserId) headers["x-user-id"] = sessionUserId;
    if (accessToken) headers["Authorization"] = `Bearer ${accessToken}`;
    return headers;
  }

  async function loadRows() {
    if (!workflowId.trim()) return;
    setBusy(true);
    setErr(null);
    setRunError(null);
    setRunNotice(null);
    setTrialCta(null);
    setPrefill(null);
    try {
      const nextRows = await loadGem5Rows(workflowId.trim());
      if (!nextRows.length) throw new Error("No gem5 result rows were found.");
      setRows(nextRows);
      const best = [...nextRows].sort((a, b) => (b.perf_per_watt || 0) - (a.perf_per_watt || 0))[0];
      setSelectedRunId((current) => current || best.run_id);
    } catch (e: unknown) {
      setErr(errorMessage(e));
    } finally {
      setBusy(false);
    }
  }

  async function generateHandoff() {
    if (!workflowId.trim()) return;
    setBusy(true);
    setErr(null);
    setRunError(null);
    setRunNotice(null);
    setTrialCta(null);
    try {
      const resp = await fetch(`${API_BASE}/apps/system/architecture/rtl-handoff/${workflowId.trim()}`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify({ selected_run_id: selected?.run_id || selectedRunId }),
      });
      const text = await resp.text();
      const data = text ? JSON.parse(text) : {};
      if (!resp.ok) throw new Error(data?.detail || `Failed to create handoff (${resp.status})`);
      const nextPrefill = data?.handoff?.arch2rtl_prefill as Arch2RtlPrefill | undefined;
      if (!nextPrefill?.specText) throw new Error("Handoff did not include an Arch2RTL prefill spec.");
      setPrefill(nextPrefill);
    } catch (e: unknown) {
      setErr(errorMessage(e));
    } finally {
      setBusy(false);
    }
  }

  function openInArch2RTL() {
    if (!prefill) return;
    window.localStorage.setItem(ARCH2RTL_HANDOFF_KEY, JSON.stringify(prefill));
    router.push("/apps/arch2rtl?handoff=system");
  }

  async function runArch2RTLNow() {
    if (!prefill) return;
    setBusy(true);
    setRunError(null);
    setRunNotice(null);
    setTrialCta(null);
    try {
      const resp = await fetch(`${API_BASE}/apps/arch2rtl/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify({
          project_name: prefill.projectName,
          top_module: prefill.topModule,
          design_language: prefill.designLanguage,
          spec_text: prefill.specText,
          toggles: {
            gen_regmap: prefill.toggles.genRegmap,
            gen_upf_lite: prefill.toggles.genUpfLite,
            gen_packaging: prefill.toggles.genPackaging,
          },
        }),
      });
      const text = await resp.text();
      const data = text ? JSON.parse(text) : {};
      if (!resp.ok) {
        const detail = data?.detail ?? data;
        const checkout = typeof detail === "object" && detail !== null ? detail : data;
        if (resp.status === 402 && checkout?.requires_checkout) {
          setTrialCta({
            message: checkout.message || "Start your 3-day trial to run the architecture-derived RTL intent.",
            checkoutUrl: checkout.checkout_url || "/pricing?trial=1",
            checkoutLabel: checkout.checkout_label || "Start 3-day trial",
          });
          return;
        }
        throw new Error(typeof detail === "string" ? detail : detail?.message || `Arch2RTL failed to start (${resp.status})`);
      }
      setArch2rtlWorkflowId(data.workflow_id);
      setWorkflowRow({ id: data.workflow_id, status: "queued", logs: "" });
      setRunNotice("Arch2RTL run started. Status and logs will update below.");
    } catch (e: unknown) {
      setRunError(errorMessage(e));
    } finally {
      setBusy(false);
    }
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
            <div className="text-sm font-medium text-emerald-200">System Loop</div>
            <h1 className="mt-1 text-3xl font-bold">Architecture-to-RTL Delivery</h1>
            <p className="mt-2 max-w-3xl text-slate-300">
              Convert a completed gem5 System Architecture run into reviewed Arch2RTL intent, traceability artifacts, and an optional Arch2RTL run.
            </p>
          </div>
          <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Apps</button>
        </div>

        <section className="mt-6 grid gap-5 lg:grid-cols-[420px_1fr]">
          <aside className="space-y-4">
            <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
              <div className="text-sm font-semibold text-slate-100">Source System Architecture run</div>
              <label className="mt-4 block">
                <span className="text-xs font-semibold text-slate-300">Workflow ID</span>
                <input value={workflowId} onChange={(e) => setWorkflowId(e.target.value)} placeholder="completed System Architecture workflow_id" className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100" />
              </label>
              <button onClick={loadRows} disabled={busy || !workflowId.trim()} className="mt-4 w-full rounded-lg bg-cyan-600 px-4 py-3 font-semibold hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700">
                {busy ? "Loading..." : "Load gem5 Results"}
              </button>
              {err ? <div className="mt-3 rounded-lg border border-red-900/60 bg-red-950/30 p-3 text-sm text-red-200">{err}</div> : null}
            </div>

            {selected ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
                <div className="text-sm font-semibold text-slate-100">Selected architecture point</div>
                <select value={selectedRunId || selected.run_id} onChange={(e) => setSelectedRunId(e.target.value)} className="mt-3 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100">
                  {rows.map((row) => <option key={row.run_id} value={row.run_id}>{row.run_id} | {row.isa} | L1D {row.l1d_size_kb}KB | L2 {row.l2_size_kb}KB | IPC {row.ipc}</option>)}
                </select>
                <div className="mt-4 grid grid-cols-2 gap-2 text-sm">
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">IPC</div><div className="text-lg font-semibold">{selected.ipc}</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">Power</div><div className="text-lg font-semibold">{selected.estimated_power_w}W</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">L1D</div><div className="text-lg font-semibold">{selected.l1d_size_kb}KB</div></div>
                  <div className="rounded-lg bg-slate-950 p-3"><div className="text-slate-400">L2</div><div className="text-lg font-semibold">{selected.l2_size_kb}KB</div></div>
                </div>
                <button onClick={generateHandoff} disabled={busy} className="mt-4 w-full rounded-lg bg-emerald-600 px-4 py-3 font-semibold hover:bg-emerald-500 disabled:cursor-not-allowed disabled:bg-slate-700">
                  {busy ? "Generating..." : "Generate RTL Intent"}
                </button>
              </div>
            ) : null}
          </aside>

          <section className="space-y-5">
            {!prefill ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-8">
                <div className="text-lg font-semibold text-slate-100">Review step</div>
                <p className="mt-2 max-w-2xl text-sm leading-6 text-slate-300">
                  Load a completed System Architecture workflow, choose a sweep point, then generate the reviewed RTL intent package. ChipLoop will create `rtl_intent.yaml`, `requirements_trace.md`, `architecture_decision.md`, and an Arch2RTL prefill.
                </p>
              </div>
            ) : (
              <>
                <div className="rounded-lg border border-slate-800 bg-slate-900/50 p-5">
                  <div className="flex flex-wrap items-center justify-between gap-3">
                    <div>
                      <div className="text-sm font-semibold text-slate-100">Review Arch2RTL intent</div>
                      <div className="mt-1 text-xs text-slate-400">Edit before opening or running Arch2RTL.</div>
                    </div>
                    <div className="flex flex-wrap gap-2">
                      <button onClick={openInArch2RTL} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-100 hover:bg-slate-800">Open in Arch2RTL</button>
                      <button onClick={runArch2RTLNow} disabled={busy} className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-semibold hover:bg-cyan-500 disabled:bg-slate-700">{busy ? "Starting..." : "Run Arch2RTL Now"}</button>
                    </div>
                  </div>
                  {runNotice ? <div className="mt-4 rounded-lg border border-emerald-800 bg-emerald-950/30 p-3 text-sm text-emerald-100">{runNotice}</div> : null}
                  {runError ? <div className="mt-4 rounded-lg border border-red-900/60 bg-red-950/30 p-3 text-sm text-red-200">{runError}</div> : null}
                  {trialCta ? (
                    <div className="mt-4 rounded-lg border border-amber-800 bg-amber-950/30 p-4 text-sm text-amber-100">
                      <div className="font-semibold">Trial required to run this RTL intent</div>
                      <p className="mt-2 leading-6 text-slate-200">{trialCta.message}</p>
                      <button onClick={() => router.push(trialCta.checkoutUrl)} className="mt-3 rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500">
                        {trialCta.checkoutLabel}
                      </button>
                    </div>
                  ) : null}
                  <div className="mt-4 grid gap-4 md:grid-cols-2">
                    <label className="block">
                      <span className="text-xs font-semibold text-slate-300">Project</span>
                      <input value={prefill.projectName} onChange={(e) => setPrefill({ ...prefill, projectName: e.target.value })} className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100" />
                    </label>
                    <label className="block">
                      <span className="text-xs font-semibold text-slate-300">Top module</span>
                      <input value={prefill.topModule} onChange={(e) => setPrefill({ ...prefill, topModule: e.target.value })} className="mt-2 w-full rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-100" />
                    </label>
                  </div>
                  <textarea value={prefill.specText} onChange={(e) => setPrefill({ ...prefill, specText: e.target.value })} className="mt-4 h-[520px] w-full rounded-lg border border-slate-800 bg-slate-950 p-4 font-mono text-sm leading-6 text-slate-100" />
                </div>

                {arch2rtlWorkflowId ? (
                  <div className="rounded-lg border border-slate-800 bg-black/30 p-5">
                    <div className="text-sm text-slate-300">Arch2RTL workflow: <span className="text-slate-100">{arch2rtlWorkflowId}</span></div>
                    <div className="mt-2 text-sm text-slate-300">status: <span className="text-cyan-200">{workflowRow?.status || "queued"}</span></div>
                    <div className="mt-3"><AskThisRunPanel workflowId={arch2rtlWorkflowId} compact /></div>
                    <div className="mt-4 max-h-72 overflow-auto rounded-lg bg-slate-950 p-3 font-mono text-xs text-slate-300">
                      {logLines.length ? logLines.map((line, index) => <div key={index}>{line}</div>) : <div>Waiting for workflow logs...</div>}
                    </div>
                  </div>
                ) : null}
              </>
            )}
          </section>
        </section>
      </div>
    </main>
  );
}
