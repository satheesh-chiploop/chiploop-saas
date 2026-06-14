"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import NextWorkflowLauncher from "@/components/NextWorkflowLauncher";
import SpecTextBox from "@/components/SpecTextBox";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type ClockRow = {
  name: string;
  port: string;
  frequency_mhz: string;
  period_ns?: number | null;
  source?: string;
  needs_user_frequency?: boolean;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs
    .split("\n")
    .map((l) => l.trimEnd())
    .filter((l) => l.trim().length > 0);
}

export default function Arch2SynthesisAppPage() {
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
  const [enableScanDft, setEnableScanDft] = useState(false);
  const [runSpec2RtlCheck, setRunSpec2RtlCheck] = useState(false);

  // --- RTL source options (to skip Arch2RTL) ---
  const [rtlSourceMode, setRtlSourceMode] = useState<"none" | "repo_path" | "paste" | "from_arch2rtl">("none");
  const [repoPath, setRepoPath] = useState("");
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [pastedRtlFilesJson, setPastedRtlFilesJson] = useState("");
  const [parentWorkflowId, setParentWorkflowId] = useState("");
  const [upstreamWorkflows, setUpstreamWorkflows] = useState<Record<string, string> | null>(null);

  // --- Synthesis knobs ---
  const [foundry, setFoundry] = useState("sky130");
  const [pdk, setPdk] = useState("sky130A");
  const [toolchain, setToolchain] = useState("openlane2");
  const [targetFreqMhz, setTargetFreqMhz] = useState<string>(""); // keep as string for input stability
  const [constraintsSdc, setConstraintsSdc] = useState("");
  const [clockRows, setClockRows] = useState<ClockRow[]>([]);
  const [resetRows, setResetRows] = useState<any[]>([]);
  const [clockProbeStatus, setClockProbeStatus] = useState("");
  const [runSynthesisClosureLoop, setRunSynthesisClosureLoop] = useState(false);
  const [maxSynthesisClosureIterations, setMaxSynthesisClosureIterations] = useState("1");
  const [allowSynthesisTimingRepair, setAllowSynthesisTimingRepair] = useState(true);
  const [allowSynthesisLecRepair, setAllowSynthesisLecRepair] = useState(true);
  const [allowSynthesisRetiming, setAllowSynthesisRetiming] = useState(false);
  const [allowSynthesisHierarchyFlattening, setAllowSynthesisHierarchyFlattening] = useState(false);
  const [stopOnSynthesisClosureFailure, setStopOnSynthesisClosureFailure] = useState(false);
  const [stopOnSynthesisLecFailure, setStopOnSynthesisLecFailure] = useState(false);

  // --- Stage control ---
  const [startStage, setStartStage] = useState<"arch2rtl" | "synth">("arch2rtl");

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

  async function getJSON<T>(path: string): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      headers: { ...authHeaders() },
    });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` - ${txt}` : ""}`);
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

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    if (params.get("handoff") !== "1") return;
    const sourceId = params.get("from_workflow_id") || params.get("source_arch2rtl_workflow_id") || "";
    if (sourceId) {
      setRtlSourceMode("from_arch2rtl");
      setFromWorkflowId(sourceId);
      setStartStage("synth");
      setTopModule((current) => current || "imported_from_arch2rtl");
      setGenUpfLite(true);
    }
    setParentWorkflowId(params.get("parent_workflow_id") || "");
    const rawUpstream = params.get("upstream_workflows");
    if (rawUpstream) {
      try {
        const parsed = JSON.parse(rawUpstream) as Record<string, string>;
        setUpstreamWorkflows(parsed && typeof parsed === "object" ? parsed : null);
      } catch {
        setUpstreamWorkflows(null);
      }
    }
  }, [loading]);

  useEffect(() => {
    if (loading || rtlSourceMode !== "from_arch2rtl" || !fromWorkflowId.trim()) return;
    let cancelled = false;
    setClockProbeStatus("Detecting clocks from Arch2RTL handoff...");
    (async () => {
      try {
        const data = await getJSON<{ clock_intent?: any }>(`/apps/digital/clock-candidates/${fromWorkflowId.trim()}`);
        if (cancelled) return;
        const clocks = Array.isArray(data.clock_intent?.clocks) ? data.clock_intent.clocks : [];
        const resets = Array.isArray(data.clock_intent?.resets) ? data.clock_intent.resets : [];
        setClockRows(clocks.map((c: any) => ({
          name: String(c.name || c.port || "clk"),
          port: String(c.port || c.name || "clk"),
          frequency_mhz: c.frequency_mhz ? String(Number(c.frequency_mhz).toFixed(3).replace(/\.?0+$/, "")) : "",
          period_ns: c.period_ns ?? null,
          source: c.source || "inferred",
          needs_user_frequency: Boolean(c.needs_user_frequency),
        })));
        setResetRows(resets);
        setClockProbeStatus(clocks.length ? "Review detected clocks before synthesis." : "No clock ports detected; enter target frequency or SDC manually.");
      } catch (e: any) {
        if (!cancelled) setClockProbeStatus(e?.message || "Clock detection failed.");
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [loading, rtlSourceMode, fromWorkflowId]);

  function updateClockFrequency(index: number, value: string) {
    setClockRows((rows) => rows.map((row, idx) => (idx === index ? { ...row, frequency_mhz: value } : row)));
  }

  function clockConstraintsPayload() {
    if (!clockRows.length) return undefined;
    return {
      source: "ui_clock_table",
      clocks: clockRows.map((row) => {
        const mhz = Number(row.frequency_mhz);
        return {
          name: row.name || row.port,
          port: row.port || row.name,
          frequency_mhz: Number.isFinite(mhz) && mhz > 0 ? mhz : undefined,
          source: row.source || "ui_clock_table",
        };
      }),
      resets: resetRows,
    };
  }

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

    const hasSpec = !!specText.trim();
    const hasRtlSource = rtlSourceMode !== "none";
    if (!topModule.trim() && !hasRtlSource) return false;

    // Require at least one: spec OR RTL source
    if (!hasSpec && !hasRtlSource) return false;

    // If repo_path selected, require repoPath
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "from_arch2rtl" && !fromWorkflowId.trim()) return false;

    return true;
  }, [running, topModule, specText, rtlSourceMode, repoPath, fromWorkflowId]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const pasted_rtl_files = rtlSourceMode === "paste" ? parseMaybeJsonArray(pastedRtlFilesJson) : undefined;

      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/arch2synthesis/run", {
        // Arch2RTL inputs (same)
        project_name: projectName || undefined,
        top_module: topModule,
        design_language: designLanguage,
        spec_text: specText || undefined,

        // RTL source (optional)
        rtl_source_mode: rtlSourceMode === "none" ? undefined : rtlSourceMode,
        repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
        from_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
        source_arch2rtl_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
        parent_workflow_id: parentWorkflowId || undefined,
        upstream_workflows: rtlSourceMode === "from_arch2rtl" ? { ...(upstreamWorkflows || {}), arch2rtl: fromWorkflowId } : undefined,
        pasted_rtl_files,

        // synthesis knobs
        foundry: foundry || undefined,
        pdk: pdk || undefined,
        toolchain: toolchain || undefined,
        target_frequency_mhz: targetFreqMhz.trim() ? Number(targetFreqMhz) : undefined,
        constraints_sdc: constraintsSdc.trim() ? constraintsSdc : undefined,
        clock_constraints: clockConstraintsPayload(),
        run_synthesis_closure_loop: runSynthesisClosureLoop,
        max_synthesis_closure_iterations: runSynthesisClosureLoop ? Number(maxSynthesisClosureIterations) : 1,
        allow_synthesis_timing_repair: allowSynthesisTimingRepair,
        allow_synthesis_lec_repair: allowSynthesisLecRepair,
        allow_synthesis_retiming: allowSynthesisRetiming,
        allow_synthesis_hierarchy_flattening: allowSynthesisHierarchyFlattening,
        stop_on_synthesis_closure_failure: stopOnSynthesisClosureFailure,
        stop_on_synthesis_lec_failure: stopOnSynthesisLecFailure,
        synthesis_closure: {
          enabled: runSynthesisClosureLoop,
          max_iterations: runSynthesisClosureLoop ? Number(maxSynthesisClosureIterations) : 1,
          allow_synthesis_timing_repair: allowSynthesisTimingRepair,
          allow_synthesis_lec_repair: allowSynthesisLecRepair,
          allow_synthesis_retiming: allowSynthesisRetiming,
          allow_synthesis_hierarchy_flattening: allowSynthesisHierarchyFlattening,
          stop_on_synthesis_closure_failure: stopOnSynthesisClosureFailure,
          stop_on_synthesis_lec_failure: stopOnSynthesisLecFailure,
        },

        // stage control
        start_stage: startStage,
        stop_stage: "synth",

        toggles: {
          gen_regmap: genRegmap,
          gen_upf_lite: genUpfLite,
          gen_packaging: genPackaging,
          enable_scan_dft: enableScanDft,
          run_spec2rtl_check: runSpec2RtlCheck,
          run_synthesis_closure_loop: runSynthesisClosureLoop,
          allow_synthesis_timing_repair: allowSynthesisTimingRepair,
          allow_synthesis_lec_repair: allowSynthesisLecRepair,
          allow_synthesis_retiming: allowSynthesisRetiming,
          allow_synthesis_hierarchy_flattening: allowSynthesisHierarchyFlattening,
          stop_on_synthesis_closure_failure: stopOnSynthesisClosureFailure,
          stop_on_synthesis_lec_failure: stopOnSynthesisLecFailure,
          skip_arch2rtl: rtlSourceMode !== "none" || startStage !== "arch2rtl",
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

        <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Arch2Synthesis</h1>
        <p className="mt-2 text-slate-300">
          Arch2RTL + Synthesis. You can also skip Arch2RTL by providing RTL input.
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
                Inherit/generate UPF-lite and run static checks
              </label>
              <label className="flex items-center gap-2 text-sm text-slate-300">
                <input type="checkbox" checked={genPackaging} onChange={(e) => setGenPackaging(e.target.checked)} />
                Generate packaging/handoff
              </label>
              <label className="flex items-center gap-2 text-sm text-slate-300">
                <input type="checkbox" checked={enableScanDft} onChange={(e) => setEnableScanDft(e.target.checked)} />
                Insert scan DFT, then run ATPG readiness
              </label>
              <label className="flex items-start gap-2 text-sm text-slate-300">
                <input className="mt-1" type="checkbox" checked={runSpec2RtlCheck} onChange={(e) => setRunSpec2RtlCheck(e.target.checked)} />
                <span>
                  Run Spec-to-RTL conformance check
                  <span className="block text-xs text-slate-500">
                    Optional: checks RTL against spec before synthesis consumes it.
                  </span>
                </span>
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
              <div className="text-sm font-semibold text-slate-200">Synthesis settings</div>

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

              {rtlSourceMode === "from_arch2rtl" ? (
                <div className="rounded-xl border border-slate-800 bg-black/30 p-3">
                  <div className="flex items-center justify-between gap-3">
                    <div className="text-sm font-semibold text-slate-200">Detected clock table</div>
                    <div className="text-xs text-slate-500">{clockProbeStatus}</div>
                  </div>
                  {clockRows.length ? (
                    <div className="mt-3 overflow-x-auto">
                      <table className="w-full text-left text-xs">
                        <thead className="text-slate-400">
                          <tr>
                            <th className="py-1 pr-2">Clock</th>
                            <th className="py-1 pr-2">Port</th>
                            <th className="py-1 pr-2">MHz</th>
                            <th className="py-1">Source</th>
                          </tr>
                        </thead>
                        <tbody>
                          {clockRows.map((clock, idx) => (
                            <tr key={`${clock.port}-${idx}`} className="border-t border-slate-800">
                              <td className="py-2 pr-2 text-slate-200">{clock.name}</td>
                              <td className="py-2 pr-2 text-slate-300">{clock.port}</td>
                              <td className="py-2 pr-2">
                                <input
                                  value={clock.frequency_mhz}
                                  onChange={(e) => updateClockFrequency(idx, e.target.value)}
                                  className="w-24 rounded-lg border border-slate-800 bg-black/40 px-2 py-1 text-slate-100"
                                  placeholder="MHz"
                                />
                              </td>
                              <td className="py-2 text-slate-500">{clock.source || "inferred"}</td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  ) : (
                    <div className="mt-2 text-xs text-slate-500">Clock rows will appear after a valid Arch2RTL workflow ID is loaded.</div>
                  )}
                  {resetRows.length ? (
                    <div className="mt-2 text-xs text-slate-500">
                      Resets: {resetRows.map((r: any) => r.port || r.name).filter(Boolean).join(", ")}
                    </div>
                  ) : null}
                </div>
              ) : null}

              <label className="block text-sm text-slate-300">SDC constraints (optional)</label>
              <textarea
                value={constraintsSdc}
                onChange={(e) => setConstraintsSdc(e.target.value)}
                rows={5}
                className="w-full rounded-2xl border border-slate-800 bg-black/30 p-3 text-slate-100"
                placeholder="create_clock ...\nset_input_delay ..."
              />

              <div className="rounded-xl border border-slate-800 bg-black/20 p-4">
                <label className="flex items-start gap-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runSynthesisClosureLoop} onChange={(e) => setRunSynthesisClosureLoop(e.target.checked)} className="mt-1" />
                  <span>Run synthesis closure loop</span>
                </label>
                {runSynthesisClosureLoop ? (
                  <div className="mt-3 space-y-3">
                    <label className="block text-sm text-slate-300">
                      Max iterations
                      <select value={maxSynthesisClosureIterations} onChange={(e) => setMaxSynthesisClosureIterations(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                        <option value="1">1</option>
                        <option value="2">2</option>
                      </select>
                    </label>
                    <div className="grid gap-2 sm:grid-cols-2">
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowSynthesisTimingRepair} onChange={(e) => setAllowSynthesisTimingRepair(e.target.checked)} /> Setup timing repair</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowSynthesisLecRepair} onChange={(e) => setAllowSynthesisLecRepair(e.target.checked)} /> Synthesis LEC repair</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowSynthesisRetiming} onChange={(e) => setAllowSynthesisRetiming(e.target.checked)} /> Allow retiming</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowSynthesisHierarchyFlattening} onChange={(e) => setAllowSynthesisHierarchyFlattening(e.target.checked)} /> Allow hierarchy flattening</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={stopOnSynthesisClosureFailure} onChange={(e) => setStopOnSynthesisClosureFailure(e.target.checked)} /> Stop downstream on closure failure</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={stopOnSynthesisLecFailure} onChange={(e) => setStopOnSynthesisLecFailure(e.target.checked)} /> Stop downstream on LEC failure</label>
                    </div>
                  </div>
                ) : null}
              </div>

              <label className="block text-sm text-slate-300">Start stage</label>
              <select
                value={startStage}
                onChange={(e) => setStartStage(e.target.value as any)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              >
                <option value="arch2rtl">arch2rtl</option>
                <option value="synth">synth</option>
              </select>
              <div className="text-xs text-slate-500">
                Use <span className="text-slate-300">synth</span> when RTL is already available.
              </div>
            </div>

            <button
              onClick={runNow}
              disabled={!canRun}
              className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${
                canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
              }`}
            >
              {running ? "Starting…" : "Run Arch2Synthesis"}
            </button>

            {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

          </div>

          {/* RIGHT: spec + logs */}
          <div className="space-y-4">
            <div className="rounded-2xl border border-slate-800 bg-black/30 p-5">
              <SpecTextBox
                label="Spec text (optional if RTL provided)"
                value={specText}
                onChange={setSpecText}
                rows={14}
                voiceTitle="Voice Spec Draft"
                voiceLoopType="digital"
                voiceTarget="Digital spec"
                uploadLabel="Upload spec"
                uploadHelper="Load a text, markdown, JSON, YAML, SystemVerilog, Verilog, or SDC spec file."
                placeholder="Paste your spec here..."
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

        {workflowId ? (
          <div className="mt-6 space-y-4">
            <div className="rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
              <div>
                workflow_id: <span className="break-all text-slate-100">{workflowId}</span>
              </div>
              <div>
                run_id: <span className="break-all text-slate-100">{runId}</span>
              </div>
              <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                Download ZIP (full=1)
              </button>
              <div className="mt-3">
                <NextWorkflowLauncher
                  currentStage="synthesis"
                  currentWorkflowId={workflowId}
                  currentRunId={runId}
                  sourceArch2RTLWorkflowId={rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : null}
                  upstreamWorkflows={rtlSourceMode === "from_arch2rtl" ? { arch2rtl: fromWorkflowId, arch2synthesis: workflowId } : undefined}
                  disabled={workflowRow?.status !== "completed"}
                />
              </div>
            </div>
            <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="synthesis" logs={workflowRow?.logs} />
            <AskThisRunPanel workflowId={workflowId} compact />
          </div>
        ) : null}
      </div>
    </main>
  );
}
