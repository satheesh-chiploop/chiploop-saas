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

export default function Arch2TapeoutAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  // --- Arch2RTL fields (same as Arch2RTL page) ---
  const [projectName, setProjectName] = useState("");
  const [topModule, setTopModule] = useState("");
  const [designLanguage, setDesignLanguage] = useState<"systemverilog" | "verilog">("systemverilog");
  const [specText, setSpecText] = useState("");

  const [genRegmap, setGenRegmap] = useState(true);
  const [genUpfLite, setGenUpfLite] = useState(false);
  const [genPackaging, setGenPackaging] = useState(true);

  // --- RTL source options (to skip Arch2RTL) ---
  const [rtlSourceMode, setRtlSourceMode] = useState<"none" | "repo_path" | "paste" | "from_arch2rtl">("none");
  const [repoPath, setRepoPath] = useState("");
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [pastedRtlFilesJson, setPastedRtlFilesJson] = useState("");

  // --- Foundry/tool knobs ---
  const [foundry, setFoundry] = useState("sky130");
  const [pdk, setPdk] = useState("sky130A");
  const [toolchain, setToolchain] = useState("openlane2");
  const [targetFreqMhz, setTargetFreqMhz] = useState<string>("");
  const [constraintsSdc, setConstraintsSdc] = useState("");

  // --- Tapeout knobs ---
  const [effort, setEffort] = useState<"fast" | "balanced" | "signoff">("balanced");
  const [runFill, setRunFill] = useState(true);
  const [runDrc, setRunDrc] = useState(true);
  const [runLvs, setRunLvs] = useState(true);

  // --- Stage control ---
  const [startStage, setStartStage] = useState<"arch2rtl" | "synth" | "floorplan">("arch2rtl");

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

      const userId = session?.user?.id || null;
      setSessionUserId(userId);
      setAccessToken(session?.access_token || null);
      setLoading(false);

      if (!userId) {
        router.push("/login");
      }
    })();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // Poll workflow row when workflowId is present
  useEffect(() => {
    if (!workflowId) return;

    let alive = true;
    const interval = setInterval(async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .maybeSingle();

      if (!alive) return;
      if (error) return;
      if (data) setWorkflowRow(data as any);
    }, 1500);

    return () => {
      alive = false;
      clearInterval(interval);
    };
  }, [workflowId]);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  function parseMaybeJsonArray(raw: string): any[] | undefined {
    const t = raw.trim();
    if (!t) return undefined;
    try {
      const v = JSON.parse(t);
      if (Array.isArray(v)) return v;
      throw new Error("Expected a JSON array");
    } catch (e: any) {
      throw new Error(`Invalid JSON for pasted RTL files: ${e?.message || String(e)}`);
    }
  }

  const canRun = useMemo(() => {
    if (running) return false;
    if (!topModule.trim()) return false;

    const hasSpec = !!specText.trim();
    const hasRtlSource = rtlSourceMode !== "none";

    if (!hasSpec && !hasRtlSource) return false;

    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "from_arch2rtl" && !fromWorkflowId.trim()) return false;

    // If user selects floorplan, they should not rely on spec-only.
    // We still allow it because your backend/workflow may decide what is needed,
    // but best practice is: floorplan requires existing netlist/config.
    return true;
  }, [running, topModule, specText, rtlSourceMode, repoPath, fromWorkflowId]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const pasted_rtl_files = rtlSourceMode === "paste" ? parseMaybeJsonArray(pastedRtlFilesJson) : undefined;

      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/arch2tapeout/run", {
        // Arch2RTL inputs (same)
        project_name: projectName || undefined,
        top_module: topModule,
        design_language: designLanguage,
        spec_text: specText || undefined,

        // RTL source (optional)
        rtl_source_mode: rtlSourceMode === "none" ? undefined : rtlSourceMode,
        repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
        from_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
        pasted_rtl_files,

        // foundry/tool knobs
        foundry: foundry || undefined,
        pdk: pdk || undefined,
        toolchain: toolchain || undefined,
        target_frequency_mhz: targetFreqMhz.trim() ? Number(targetFreqMhz) : undefined,
        constraints_sdc: constraintsSdc.trim() ? constraintsSdc : undefined,

        // tapeout knobs
        effort,
        run_fill: runFill,
        run_drc: runDrc,
        run_lvs: runLvs,

        // stage control
        start_stage: startStage,
        stop_stage: "tapeout",

        toggles: {
          gen_regmap: genRegmap,
          gen_upf_lite: genUpfLite,
          gen_packaging: genPackaging,
          skip_arch2rtl: rtlSourceMode !== "none" || startStage !== "arch2rtl",
          // (optional future: if your workflow supports it)
          // skip_synth: startStage === "floorplan",
        },
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
    <main className="min-h-screen bg-black text-white px-6 py-10">
      <div className="mx-auto max-w-6xl">
        <div className="inline-flex items-center rounded-full border border-slate-800 bg-black/30 px-3 py-1 text-xs text-slate-300">
          ⚡ Digital Loop
        </div>

        <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Arch2Tapeout</h1>
        <p className="mt-2 text-slate-300">
          Arch2RTL + Synthesis + RTL→GDS flow. You can start from RTL (or later: floorplan) for partial runs.
        </p>

        <div className="mt-6 grid gap-4 md:grid-cols-2">
          {/* LEFT: inputs */}
          <div className="space-y-3 rounded-2xl border border-slate-800 bg-black/30 p-5">
            <label className="block text-sm text-slate-300">Project name (optional)</label>
            <input
              value={projectName}
              onChange={(e) => setProjectName(e.target.value)}
              className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
            />

            <label className="block text-sm text-slate-300">Top module *</label>
            <input
              value={topModule}
              onChange={(e) => setTopModule(e.target.value)}
              className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
            />

            <label className="block text-sm text-slate-300">Design language</label>
            <select
              value={designLanguage}
              onChange={(e) => setDesignLanguage(e.target.value as any)}
              className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
            >
              <option value="systemverilog">SystemVerilog</option>
              <option value="verilog">Verilog</option>
            </select>

            <div className="mt-3 space-y-2">
              <label className="flex items-center gap-2 text-sm text-slate-300">
                <input type="checkbox" checked={genRegmap} onChange={(e) => setGenRegmap(e.target.checked)} />
                Generate regmap
              </label>
              <label className="flex items-center gap-2 text-sm text-slate-300">
                <input type="checkbox" checked={genUpfLite} onChange={(e) => setGenUpfLite(e.target.checked)} />
                Generate UPF-lite
              </label>
              <label className="flex items-center gap-2 text-sm text-slate-300">
                <input type="checkbox" checked={genPackaging} onChange={(e) => setGenPackaging(e.target.checked)} />
                Generate packaging/handoff
              </label>
            </div>

            <div className="mt-4 border-t border-slate-800 pt-4 space-y-3">
              <div className="text-sm font-semibold text-slate-200">RTL source (optional)</div>

              <label className="block text-sm text-slate-300">RTL source mode</label>
              <select
                value={rtlSourceMode}
                onChange={(e) => setRtlSourceMode(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="none">None (use Arch2RTL spec → RTL)</option>
                <option value="repo_path">Repo path</option>
                <option value="paste">Paste RTL files (JSON array)</option>
                <option value="from_arch2rtl">From prior Arch2RTL workflow_id</option>
              </select>

              {rtlSourceMode === "repo_path" ? (
                <>
                  <label className="block text-sm text-slate-300">Repo path *</label>
                  <input
                    value={repoPath}
                    onChange={(e) => setRepoPath(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="/path/to/rtl"
                  />
                </>
              ) : null}

              {rtlSourceMode === "from_arch2rtl" ? (
                <>
                  <label className="block text-sm text-slate-300">Source workflow_id *</label>
                  <input
                    value={fromWorkflowId}
                    onChange={(e) => setFromWorkflowId(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                    placeholder="workflow UUID"
                  />
                </>
              ) : null}

              {rtlSourceMode === "paste" ? (
                <>
                  <label className="block text-sm text-slate-300">Pasted RTL files JSON *</label>
                  <textarea
                    value={pastedRtlFilesJson}
                    onChange={(e) => setPastedRtlFilesJson(e.target.value)}
                    rows={6}
                    className="w-full rounded-2xl border border-slate-800 bg-black/30 p-3 text-slate-100"
                    placeholder='[{"path":"rtl/top.sv","content":"module ... endmodule"}]'
                  />
                  <div className="text-xs text-slate-500">Must be a JSON array of {`{path, content}`} objects.</div>
                </>
              ) : null}
            </div>

            <div className="mt-4 border-t border-slate-800 pt-4 space-y-3">
              <div className="text-sm font-semibold text-slate-200">Tapeout settings</div>

              <div className="grid grid-cols-1 gap-3 md:grid-cols-3">
                <div>
                  <label className="block text-sm text-slate-300">Foundry</label>
                  <input
                    value={foundry}
                    onChange={(e) => setFoundry(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  />
                </div>
                <div>
                  <label className="block text-sm text-slate-300">PDK</label>
                  <input
                    value={pdk}
                    onChange={(e) => setPdk(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  />
                </div>
                <div>
                  <label className="block text-sm text-slate-300">Toolchain</label>
                  <input
                    value={toolchain}
                    onChange={(e) => setToolchain(e.target.value)}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  />
                </div>
              </div>

              <label className="block text-sm text-slate-300">Target frequency (MHz)</label>
              <input
                value={targetFreqMhz}
                onChange={(e) => setTargetFreqMhz(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                placeholder="e.g., 250"
              />

              <label className="block text-sm text-slate-300">SDC constraints (optional)</label>
              <textarea
                value={constraintsSdc}
                onChange={(e) => setConstraintsSdc(e.target.value)}
                rows={5}
                className="w-full rounded-2xl border border-slate-800 bg-black/30 p-3 text-slate-100"
                placeholder="create_clock ...\nset_input_delay ..."
              />

              <label className="block text-sm text-slate-300">Effort</label>
              <select
                value={effort}
                onChange={(e) => setEffort(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="fast">fast</option>
                <option value="balanced">balanced</option>
                <option value="signoff">signoff</option>
              </select>

              <div className="mt-2 space-y-2">
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={runFill} onChange={(e) => setRunFill(e.target.checked)} />
                  Run fill
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={runDrc} onChange={(e) => setRunDrc(e.target.checked)} />
                  Run DRC
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={runLvs} onChange={(e) => setRunLvs(e.target.checked)} />
                  Run LVS
                </label>
              </div>

              <label className="block text-sm text-slate-300 mt-2">Start stage</label>
              <select
                value={startStage}
                onChange={(e) => setStartStage(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="arch2rtl">arch2rtl</option>
                <option value="synth">synth</option>
                <option value="floorplan">floorplan</option>
              </select>
              <div className="text-xs text-slate-500">
                Use <span className="text-slate-300">synth</span> when RTL exists;{" "}
                <span className="text-slate-300">floorplan</span> is for advanced partial runs (requires prior artifacts).
              </div>
            </div>

            <button
              onClick={runNow}
              disabled={!canRun}
              className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${
                canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
              }`}
            >
              {running ? "Starting…" : "Run Arch2Tapeout"}
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
                <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                  Download ZIP (full=1)
                </button>
              </div>
            ) : null}
          </div>

          {/* RIGHT: spec + logs */}
          <div className="space-y-4">
            <div className="rounded-2xl border border-slate-800 bg-black/30 p-5">
              <label className="block text-sm text-slate-300">Spec text (optional if RTL provided)</label>
              <textarea
                value={specText}
                onChange={(e) => setSpecText(e.target.value)}
                rows={14}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste your spec here…"
              />
              <div className="mt-2 text-xs text-slate-500">Tip: keep it structured (interfaces, clocks, resets, targets).</div>
            </div>

            <div className="rounded-2xl border border-slate-800 bg-black/30 p-5">
              <div className="flex items-center justify-between">
                <div className="text-sm font-semibold text-slate-200">Live run logs</div>
                <div className="text-xs text-slate-400">
                  {workflowRow?.status ? `status: ${workflowRow.status}` : "—"}
                  {workflowRow?.phase ? ` · phase: ${workflowRow.phase}` : ""}
                </div>
              </div>

              <div
                ref={logsRef}
                className="mt-3 h-64 overflow-y-auto rounded-xl border border-slate-800 bg-black/40 p-3 font-mono text-xs text-slate-200"
              >
                {logLines.length === 0 ? (
                  <div className="text-slate-500">No logs yet…</div>
                ) : (
                  logLines.map((l, i) => (
                    <div key={i} className="whitespace-pre-wrap">
                      {l}
                    </div>
                  ))
                )}
              </div>
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}