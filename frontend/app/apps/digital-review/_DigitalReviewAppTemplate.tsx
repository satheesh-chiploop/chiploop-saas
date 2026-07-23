"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import { FPGA_BITSTREAM_PREFILL_KEY } from "@/lib/pwmFullStackDemo";
import SpecTextBox from "@/components/SpecTextBox";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type FieldKind = "source" | "rtl" | "sdc" | "timing" | "frequency" | "stage" | "depth" | "notes" | "fpga";

type Props = {
  slug: string;
  title: string;
  subtitle: string;
  runPath: string;
  dashboardStage: "rtl_review" | "constraint_review" | "timing_debug" | "fpga";
  fields: FieldKind[];
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter(Boolean);
}

export default function DigitalReviewAppTemplate({ slug, title, subtitle, runPath, dashboardStage, fields }: Props) {
  const router = useRouter();
  const logsRef = useRef<HTMLDivElement | null>(null);

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  const [sourceMode, setSourceMode] = useState<"from_arch2rtl" | "paste" | "repo_path">("from_arch2rtl");
  const [sourceWorkflowId, setSourceWorkflowId] = useState("");
  const [repoPath, setRepoPath] = useState("");
  const [rtlText, setRtlText] = useState("");
  const [sdcText, setSdcText] = useState("");
  const [timingText, setTimingText] = useState("");
  const [targetFrequency, setTargetFrequency] = useState("100");
  const [stage, setStage] = useState("auto");
  const [reviewDepth, setReviewDepth] = useState("standard");
  const [notes, setNotes] = useState("");
  const [board, setBoard] = useState("icebreaker");
  const [topModule, setTopModule] = useState("");
  const [pcfText, setPcfText] = useState("");
  const [runFpgaSynthesisClosureLoop, setRunFpgaSynthesisClosureLoop] = useState(false);
  const [maxFpgaSynthesisClosureIterations, setMaxFpgaSynthesisClosureIterations] = useState("1");
  const [runFpgaTimingClosureLoop, setRunFpgaTimingClosureLoop] = useState(true);
  const [maxFpgaTimingClosureIterations, setMaxFpgaTimingClosureIterations] = useState("3");
  const [allowYosysFlatten, setAllowYosysFlatten] = useState(true);
  const [allowNextpnrSeedSweep, setAllowNextpnrSeedSweep] = useState(true);
  const [allowFrequencyRelaxation, setAllowFrequencyRelaxation] = useState(false);
  const [contextMode, setContextMode] = useState<"smart" | "full">("smart");
  const [hemEnabled, setHemEnabled] = useState(false);
  const [hemMode, setHemMode] = useState<"fixed" | "adaptive">("fixed");

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  useEffect(() => {
    (async () => {
      setLoading(true);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace(`/login?next=/apps/${slug}`);
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router, slug]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    const source = params.get("from_workflow_id") || params.get("source_workflow_id") || "";
    if (source) {
      setSourceMode("from_arch2rtl");
      setSourceWorkflowId(source);
    }
    if (!fields.includes("fpga")) return;
    const raw = window.localStorage.getItem(FPGA_BITSTREAM_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as Partial<{
        rtlSourceMode: "from_arch2rtl" | "paste" | "repo_path";
        sourceWorkflowId: string;
        repoPath: string;
        rtlText: string;
        board: string;
        topModule: string;
        targetFrequency: string;
        pcfText: string;
        notes: string;
        hemEnabled: boolean;
        hemMode: "fixed" | "adaptive";
      }>;
      if (prefill.rtlSourceMode) setSourceMode(prefill.rtlSourceMode);
      if (prefill.sourceWorkflowId) setSourceWorkflowId(prefill.sourceWorkflowId);
      if (prefill.repoPath) setRepoPath(prefill.repoPath);
      if (prefill.rtlText) setRtlText(prefill.rtlText);
      if (prefill.board) setBoard(prefill.board);
      if (prefill.topModule) setTopModule(prefill.topModule);
      if (prefill.targetFrequency) setTargetFrequency(prefill.targetFrequency);
      if (prefill.pcfText) setPcfText(prefill.pcfText);
      if (prefill.notes) setNotes(prefill.notes);
      if (typeof prefill.hemEnabled === "boolean") setHemEnabled(prefill.hemEnabled);
      if (prefill.hemMode) setHemMode(prefill.hemMode);
    } catch {
      // Ignore malformed local prefill.
    } finally {
      window.localStorage.removeItem(FPGA_BITSTREAM_PREFILL_KEY);
    }
  }, [loading]);

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
    const headers: Record<string, string> = {};
    if (sessionUserId) headers["x-user-id"] = sessionUserId;
    if (accessToken) headers.Authorization = `Bearer ${accessToken}`;
    return headers;
  }

  const canRun = useMemo(() => {
    if (running) return false;
    if (fields.includes("timing")) return Boolean(sourceWorkflowId.trim() || timingText.trim());
    if (sourceMode === "from_arch2rtl") return Boolean(sourceWorkflowId.trim());
    if (sourceMode === "repo_path") return Boolean(repoPath.trim());
    return Boolean(rtlText.trim());
  }, [fields, running, sourceMode, sourceWorkflowId, repoPath, rtlText, timingText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const body: Record<string, any> = {
        rtl_source_mode: sourceMode,
        from_workflow_id: sourceMode === "from_arch2rtl" ? sourceWorkflowId.trim() : undefined,
        source_arch2rtl_workflow_id: sourceMode === "from_arch2rtl" ? sourceWorkflowId.trim() : undefined,
        source_workflow_id: sourceWorkflowId.trim() || undefined,
        repo_path: sourceMode === "repo_path" ? repoPath.trim() : undefined,
        rtl_text: sourceMode === "paste" ? rtlText : undefined,
        pasted_rtl_files: sourceMode === "paste" && rtlText.trim() ? [{ path: "rtl/review_input.sv", content: rtlText }] : undefined,
        constraints_sdc: sdcText.trim() || undefined,
        timing_report_text: timingText.trim() || undefined,
        target_frequency_mhz: targetFrequency ? Number(targetFrequency) : undefined,
        stage,
        review_depth: reviewDepth,
        board: fields.includes("fpga") ? board : undefined,
        family: fields.includes("fpga") ? "ice40" : undefined,
        top_module: fields.includes("fpga") && topModule.trim() ? topModule.trim() : undefined,
        pcf_text: fields.includes("fpga") && pcfText.trim() ? pcfText : undefined,
        notes: notes.trim() || undefined,
        run_fpga_synthesis_closure_loop: fields.includes("fpga") ? runFpgaSynthesisClosureLoop : undefined,
        max_fpga_synthesis_closure_iterations: fields.includes("fpga") ? Number(maxFpgaSynthesisClosureIterations || 1) : undefined,
        run_fpga_timing_closure_loop: fields.includes("fpga") ? runFpgaTimingClosureLoop : undefined,
        max_fpga_timing_closure_iterations: fields.includes("fpga") ? Number(maxFpgaTimingClosureIterations || 1) : undefined,
        allow_yosys_flatten: fields.includes("fpga") ? allowYosysFlatten : undefined,
        allow_nextpnr_seed_sweep: fields.includes("fpga") ? allowNextpnrSeedSweep : undefined,
        allow_frequency_relaxation: fields.includes("fpga") ? allowFrequencyRelaxation : undefined,
        smart_context_enabled: fields.includes("fpga") ? contextMode === "smart" : undefined,
        context_mode: fields.includes("fpga") ? contextMode : undefined,
        hem_enabled: fields.includes("fpga") ? hemEnabled : undefined,
        hem_mode: fields.includes("fpga") ? hemMode : undefined,
      };
      const resp = await fetch(`${API_BASE}${runPath}`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(body),
      });
      if (!resp.ok) {
        const text = await resp.text().catch(() => "");
        throw new Error(`${resp.status} ${resp.statusText}${text ? ` - ${text}` : ""}`);
      }
      const out = await resp.json();
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
        <div className="text-slate-300">Loading...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-[1440px] px-6 py-10">
        <div className="flex items-center justify-between gap-3">
          <button onClick={() => router.push("/apps")} className="rounded-xl border border-slate-700 px-4 py-2 text-slate-200 hover:border-cyan-400">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 text-slate-200 hover:border-cyan-400">
            Studio
          </button>
        </div>

        <section className="mt-6 rounded-2xl border border-cyan-500/40 bg-slate-950/80 p-6 shadow-[0_0_0_1px_rgba(34,211,238,0.08)]">
          <div className="text-sm font-semibold uppercase tracking-[0.18em] text-cyan-300">{fields.includes("fpga") ? "FPGA Loop" : "Digital Loop"}</div>
          <h1 className="mt-2 text-3xl font-black text-white md:text-4xl">{title}</h1>
          <p className="mt-3 max-w-3xl text-base leading-7 text-slate-300">{subtitle}</p>

          <div className="mt-6 grid gap-5 lg:grid-cols-[minmax(0,1fr)_420px]">
            <div className="space-y-4">
              {fields.includes("source") ? (
                <div className="grid gap-3 md:grid-cols-3">
                  <label className="block">
                    <span className="text-sm text-slate-300">Source</span>
                    <select value={sourceMode} onChange={(e) => setSourceMode(e.target.value as any)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      <option value="from_arch2rtl">Prior workflow</option>
                      <option value="paste">Paste RTL</option>
                      <option value="repo_path">Repo/path</option>
                    </select>
                  </label>
                  <label className="block md:col-span-2">
                    <span className="text-sm text-slate-300">{sourceMode === "repo_path" ? "Repo/path" : "Source workflow ID"}</span>
                    <input
                      value={sourceMode === "repo_path" ? repoPath : sourceWorkflowId}
                      onChange={(e) => (sourceMode === "repo_path" ? setRepoPath(e.target.value) : setSourceWorkflowId(e.target.value))}
                      className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white"
                      placeholder={sourceMode === "repo_path" ? "C:/path/to/repo or /repo/path" : "Workflow ID"}
                    />
                  </label>
                </div>
              ) : null}

              {fields.includes("fpga") && (fields.includes("rtl") || sourceMode === "paste") ? (
                <SpecTextBox
                  label="RTL / FPGA source"
                  value={rtlText}
                  onChange={setRtlText}
                  rows={9}
                  voiceTitle="FPGA RTL Voice Input"
                  voiceLoopType="fpga"
                  voiceTarget="RTL source, board notes, or FPGA prototype intent"
                  uploadLabel="Upload RTL"
                  uploadHelper="Upload Verilog/SystemVerilog, board notes, or small source snippets."
                  placeholder="Paste Verilog/SystemVerilog RTL or upload source files."
                  textareaClassName="w-full resize-y bg-transparent p-1 font-mono text-sm text-slate-100 outline-none"
                />
              ) : fields.includes("rtl") || sourceMode === "paste" ? (
                <label className="block">
                  <span className="text-sm text-slate-300">RTL text</span>
                  <textarea value={rtlText} onChange={(e) => setRtlText(e.target.value)} rows={8} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              {fields.includes("sdc") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Constraints SDC</span>
                  <textarea value={sdcText} onChange={(e) => setSdcText(e.target.value)} rows={7} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              {fields.includes("timing") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Timing report text</span>
                  <textarea value={timingText} onChange={(e) => setTimingText(e.target.value)} rows={9} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 font-mono text-sm text-white" />
                </label>
              ) : null}

              <div className="grid gap-3 md:grid-cols-3">
                {fields.includes("fpga") ? (
                  <>
                    <label className="block">
                      <span className="text-sm text-slate-300">Board</span>
                      <select value={board} onChange={(e) => setBoard(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                        <option value="icebreaker">Lattice iCEBreaker</option>
                        <option value="upduino_v3">UPduino v3</option>
                        <option value="icestick">Lattice iCEstick</option>
                        <option value="custom_ice40">Custom iCE40</option>
                      </select>
                    </label>
                    <label className="block">
                      <span className="text-sm text-slate-300">Top module</span>
                      <input value={topModule} onChange={(e) => setTopModule(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" placeholder="auto-detect if blank" />
                    </label>
                  </>
                ) : null}
                {fields.includes("frequency") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Target MHz</span>
                    <input value={targetFrequency} onChange={(e) => setTargetFrequency(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                  </label>
                ) : null}
                {fields.includes("stage") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Stage</span>
                    <select value={stage} onChange={(e) => setStage(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      {["auto", "synthesis", "preplace", "postplace", "postcts", "postroute", "postfill"].map((item) => <option key={item} value={item}>{item}</option>)}
                    </select>
                  </label>
                ) : null}
                {fields.includes("depth") ? (
                  <label className="block">
                    <span className="text-sm text-slate-300">Review depth</span>
                    <select value={reviewDepth} onChange={(e) => setReviewDepth(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white">
                      <option value="quick">quick</option>
                      <option value="standard">standard</option>
                      <option value="deep">deep</option>
                    </select>
                  </label>
                ) : null}
              </div>

              {fields.includes("fpga") ? (
                <div className="space-y-4">
                  <SpecTextBox
                    label="Pin constraints PCF"
                    value={pcfText}
                    onChange={setPcfText}
                    rows={7}
                    voiceTitle="FPGA Constraint Voice Input"
                    voiceLoopType="fpga"
                    voiceTarget="PCF pin constraints or board pin mapping"
                    uploadLabel="Upload PCF"
                    uploadHelper="Upload PCF constraints, board pin notes, or implementation constraints."
                    placeholder={'set_io clk 35\nset_io reset_n 10\nset_io led 99'}
                    textareaClassName="w-full resize-y bg-transparent p-1 font-mono text-sm text-slate-100 outline-none"
                  />
                  <span className="block text-xs text-amber-200">Use real board pin names before programming hardware. Blank PCF creates a starter file only.</span>

                  <div className="rounded-2xl border border-cyan-500/30 bg-cyan-950/10 p-4">
                    <div className="text-sm font-bold text-cyan-200">FPGA closure and intelligence</div>
                    <div className="mt-3 grid gap-3 md:grid-cols-2">
                      <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/30 p-3 text-sm text-slate-200">
                        <input type="checkbox" checked={runFpgaSynthesisClosureLoop} onChange={(e) => setRunFpgaSynthesisClosureLoop(e.target.checked)} className="mt-1" />
                        <span>
                          <span className="block font-semibold text-white">Synthesis closure loop</span>
                          <span className="text-slate-400">Retry synthesis with safe settings when Yosys reports fixable issues.</span>
                        </span>
                      </label>
                      <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/30 p-3 text-sm text-slate-200">
                        <input type="checkbox" checked={runFpgaTimingClosureLoop} onChange={(e) => setRunFpgaTimingClosureLoop(e.target.checked)} className="mt-1" />
                        <span>
                          <span className="block font-semibold text-white">Timing closure loop</span>
                          <span className="text-slate-400">Rerun implementation with nextpnr seed exploration when timing misses.</span>
                        </span>
                      </label>
                    </div>
                    <div className="mt-3 grid gap-3 md:grid-cols-4">
                      <label className="block">
                        <span className="text-xs uppercase tracking-wide text-slate-400">Synth tries</span>
                        <input value={maxFpgaSynthesisClosureIterations} onChange={(e) => setMaxFpgaSynthesisClosureIterations(e.target.value)} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white" />
                      </label>
                      <label className="block">
                        <span className="text-xs uppercase tracking-wide text-slate-400">Timing tries</span>
                        <input value={maxFpgaTimingClosureIterations} onChange={(e) => setMaxFpgaTimingClosureIterations(e.target.value)} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white" />
                      </label>
                      <label className="block">
                        <span className="text-xs uppercase tracking-wide text-slate-400">Context</span>
                        <select value={contextMode} onChange={(e) => setContextMode(e.target.value as "smart" | "full")} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white">
                          <option value="smart">Smart</option>
                          <option value="full">Full</option>
                        </select>
                      </label>
                      <label className="block">
                        <span className="text-xs uppercase tracking-wide text-slate-400">HEM mode</span>
                        <select value={hemMode} onChange={(e) => setHemMode(e.target.value as "fixed" | "adaptive")} disabled={!hemEnabled} className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-white disabled:opacity-50">
                          <option value="fixed">Fixed</option>
                          <option value="adaptive">Adaptive</option>
                        </select>
                      </label>
                    </div>
                    <div className="mt-3 grid gap-3 md:grid-cols-4">
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowYosysFlatten} onChange={(e) => setAllowYosysFlatten(e.target.checked)} /> Allow Yosys flatten</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowNextpnrSeedSweep} onChange={(e) => setAllowNextpnrSeedSweep(e.target.checked)} /> Seed sweep</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={allowFrequencyRelaxation} onChange={(e) => setAllowFrequencyRelaxation(e.target.checked)} /> Suggest relaxed clock</label>
                      <label className="flex items-center gap-2 text-sm text-slate-300"><input type="checkbox" checked={hemEnabled} onChange={(e) => setHemEnabled(e.target.checked)} /> HEM run memory</label>
                    </div>
                  </div>
                </div>
              ) : null}

              {fields.includes("notes") ? (
                <label className="block">
                  <span className="text-sm text-slate-300">Notes</span>
                  <textarea value={notes} onChange={(e) => setNotes(e.target.value)} rows={3} className="mt-2 w-full rounded-xl border border-slate-700 bg-black/40 px-4 py-3 text-white" />
                </label>
              ) : null}

              {err ? <div className="rounded-xl border border-rose-500/40 bg-rose-950/40 p-3 text-sm text-rose-200">{err}</div> : null}

              <div className="flex flex-wrap gap-3">
                <button disabled={!canRun} onClick={runNow} className="rounded-xl bg-cyan-400 px-5 py-3 font-bold text-slate-950 disabled:cursor-not-allowed disabled:opacity-50">
                  {running ? "Running..." : `Run ${title}`}
                </button>
                <button disabled={!workflowId} onClick={downloadZip} className="rounded-xl border border-slate-700 px-5 py-3 font-semibold text-slate-200 disabled:opacity-50">
                  Download ZIP
                </button>
              </div>
            </div>

            <aside className="rounded-xl border border-slate-800 bg-black/30 p-4">
              <div className="flex items-center justify-between">
                <div>
                  <div className="text-sm text-slate-400">Workflow</div>
                  <div className="mt-1 break-all text-sm text-cyan-200">{workflowId || "Not started"}</div>
                </div>
                <div className="rounded-full border border-slate-700 px-3 py-1 text-xs uppercase text-slate-300">{workflowRow?.status || "idle"}</div>
              </div>
              <div ref={logsRef} className="mt-4 h-[420px] overflow-auto rounded-lg bg-black/50 p-3 font-mono text-xs text-slate-300">
                {logLines.length ? logLines.map((line, idx) => <div key={`${idx}-${line}`}>{line}</div>) : <div className="text-slate-500">Logs will appear here.</div>}
              </div>
            </aside>
          </div>
        </section>

        {workflowId ? (
          <section className="mt-6 space-y-6">
            <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage={dashboardStage} logs={workflowRow?.logs} />
            <AskThisRunPanel workflowId={workflowId} />
          </section>
        ) : null}
      </div>
    </main>
  );
}
