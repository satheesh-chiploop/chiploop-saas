"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import SpecTextBox from "@/components/SpecTextBox";
import TextFileUpload from "@/components/TextFileUpload";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import { DESIGN_CHAIN_CONTEXT_KEY, type DesignChainContext } from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((l) => l.trimEnd()).filter((l) => l.trim().length > 0);
}

export default function SystemPDAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");

  // Intake
  const [projectName, setProjectName] = useState("");

  const [digitalSpecText, setDigitalSpecText] = useState("");
  const [analogSpecText, setAnalogSpecText] = useState("");
  const [socIntegrationSpecText, setSocIntegrationSpecText] = useState("");
  const [foundry, setFoundry] = useState("sky130");
  const [pdk, setPdk] = useState("sky130A");
  const [toolchain, setToolchain] = useState("openlane2");
  const [targetFreqMhz, setTargetFreqMhz] = useState("");
  const [constraintsSdc, setConstraintsSdc] = useState("");
  const [effort, setEffort] = useState<"fast" | "balanced" | "signoff">("balanced");
  const [runFill, setRunFill] = useState(true);
  const [runDrc, setRunDrc] = useState(true);
  const [runLvs, setRunLvs] = useState(true);
  const [runSpec2RtlCheck, setRunSpec2RtlCheck] = useState(false);
  const [enableScanDft, setEnableScanDft] = useState(false);
  const [analogPhysicalMode, setAnalogPhysicalMode] = useState<"blackbox" | "generate_sky130_gds" | "provided_gds">("blackbox");
  const [analogPdk, setAnalogPdk] = useState("sky130A");
  const [hasProvidedSpice, setHasProvidedSpice] = useState(false);
  const [analogSpiceText, setAnalogSpiceText] = useState("");
  const [spiceUploadMode, setSpiceUploadMode] = useState<"append" | "replace">("replace");
  const [nextFlow, setNextFlow] = useState<"system-firmware">("system-firmware");

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
        router.replace("/login?next=/apps/system-pd");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    try {
      const context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
      if (context.systemRtlWorkflowId) setSystemRtlWorkflowId(context.systemRtlWorkflowId);
    } catch {
      // ignore malformed handoff context
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
    if (systemRtlWorkflowId.trim()) return true;
    if (!digitalSpecText.trim()) return false;
    if (!analogSpecText.trim()) return false;
    if (!socIntegrationSpecText.trim()) return false;
    return true;
  }, [running, systemRtlWorkflowId, digitalSpecText, analogSpecText, socIntegrationSpecText]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const freq = Number(targetFreqMhz);
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/system/pd/run",
        {
          project_name: projectName || undefined,
          rtl_source_mode: systemRtlWorkflowId.trim() ? "from_system_rtl" : undefined,
          system_rtl_workflow_id: systemRtlWorkflowId.trim() || undefined,
          from_workflow_id: systemRtlWorkflowId.trim() || undefined,
          digital_spec_text: digitalSpecText,
          analog_spec_text: analogSpecText,
          soc_integration_spec_text: socIntegrationSpecText,
          foundry,
          pdk,
          toolchain,
          target_frequency_mhz: Number.isFinite(freq) && freq > 0 ? freq : undefined,
          constraints_sdc: constraintsSdc || undefined,
          effort,
          run_fill: runFill,
          run_drc: runDrc,
          run_lvs: runLvs,
          analog_physical_mode: analogPhysicalMode,
          analog_pdk: analogPdk,
          analog_spice_text: hasProvidedSpice ? analogSpiceText || undefined : undefined,
          toggles: {
            run_spec2rtl_check: runSpec2RtlCheck,
            enable_scan_dft: enableScanDft,
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

  function openNextFlow() {
    if (!workflowId || typeof window === "undefined") return;
    const sourceSystemRtlWorkflowId = systemRtlWorkflowId.trim() || workflowId;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.systemRtlWorkflowId = sourceSystemRtlWorkflowId;
    context.systemPdWorkflowId = workflowId;
    context.systemPdRunId = runId || undefined;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    router.push(`/apps/${nextFlow}?handoff=1&from_workflow_id=${encodeURIComponent(sourceSystemRtlWorkflowId)}&parent_workflow_id=${encodeURIComponent(workflowId)}`);
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
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">System PD</h1>
          <p className="mt-2 text-slate-300">System RTL2GDS with synthesis, synthesis LEC, scan DFT, ATPG, STA, DRC/LVS/XOR, tapeout, and tapeout LEC evidence.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input
                value={projectName}
                onChange={(e) => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
              />
              <label className="block text-sm text-slate-300">
                System RTL workflow id
                <input
                  value={systemRtlWorkflowId}
                  onChange={(e) => setSystemRtlWorkflowId(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="Optional: continue from System RTL"
                />
              </label>
              <div className="grid gap-3 sm:grid-cols-3">
                <label className="block text-sm text-slate-300">
                  Foundry
                  <input value={foundry} onChange={(e) => setFoundry(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />
                </label>
                <label className="block text-sm text-slate-300">
                  PDK
                  <input value={pdk} onChange={(e) => setPdk(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />
                </label>
                <label className="block text-sm text-slate-300">
                  Toolchain
                  <input value={toolchain} onChange={(e) => setToolchain(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />
                </label>
              </div>

              <label className="block text-sm text-slate-300">
                Target frequency MHz
                <input value={targetFreqMhz} onChange={(e) => setTargetFreqMhz(e.target.value)} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Optional" />
              </label>

              <label className="block text-sm text-slate-300">
                SDC constraints
                <textarea value={constraintsSdc} onChange={(e) => setConstraintsSdc(e.target.value)} rows={4} className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100" placeholder="Optional create_clock / constraints" />
              </label>

              <label className="block text-sm text-slate-300">
                Implementation effort
                <select value={effort} onChange={(e) => setEffort(e.target.value as "fast" | "balanced" | "signoff")} className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                  <option value="fast">Fast</option>
                  <option value="balanced">Balanced</option>
                  <option value="signoff">Signoff</option>
                </select>
              </label>

              <div className="rounded-xl border border-slate-800 bg-black/20 p-4">
                <label className="block text-sm text-slate-300">
                  Analog physical mode
                  <select
                    value={analogPhysicalMode}
                    onChange={(e) => setAnalogPhysicalMode(e.target.value as "blackbox" | "generate_sky130_gds" | "provided_gds")}
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  >
                    <option value="blackbox">Black-box analog macros</option>
                    <option value="generate_sky130_gds">Generate analog GDS - Sky130</option>
                    <option value="provided_gds">Use provided analog GDS</option>
                  </select>
                </label>
                {analogPhysicalMode === "generate_sky130_gds" ? (
                  <div className="mt-3 space-y-3">
                    <label className="block text-sm text-slate-300">
                      Analog PDK
                      <select
                        value={analogPdk}
                        onChange={(e) => setAnalogPdk(e.target.value)}
                        className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                      >
                        <option value="sky130A">Sky130A</option>
                      </select>
                    </label>
                    <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                      <input
                        type="checkbox"
                        checked={hasProvidedSpice}
                        onChange={(e) => setHasProvidedSpice(e.target.checked)}
                        className="mt-1"
                      />
                      <span>I have a Sky130 transistor-level SPICE netlist</span>
                    </label>
                    {hasProvidedSpice ? (
                      <div className="rounded-xl border border-slate-800 bg-black/20 p-3">
                        <label className="block text-sm text-slate-300">
                          Sky130 transistor-level SPICE
                          <textarea
                            value={analogSpiceText}
                            onChange={(e) => setAnalogSpiceText(e.target.value)}
                            rows={7}
                            className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                            placeholder=".subckt analog_macro vin vout vdd vss&#10;M1 ... sky130_fd_pr__nfet_01v8 W=... L=...&#10;.ends analog_macro"
                          />
                        </label>
                        <div className="mt-3 flex items-center justify-end gap-2">
                          <select
                            value={spiceUploadMode}
                            onChange={(e) => setSpiceUploadMode(e.target.value as "append" | "replace")}
                            className="h-9 rounded-lg border border-slate-800 bg-black/40 px-2 text-xs text-slate-200"
                          >
                            <option value="replace">Replace</option>
                            <option value="append">Append</option>
                          </select>
                          <TextFileUpload
                            compact
                            inline
                            showMode={false}
                            mode={spiceUploadMode}
                            onModeChange={setSpiceUploadMode}
                            accept=".spice,.spi,.cir,.ckt,.txt"
                            label="Upload SPICE netlist"
                            onText={(text, _fileName, mode) => {
                              setAnalogSpiceText((current) => mode === "append" ? [current.trim(), text.trim()].filter(Boolean).join("\n\n") : text);
                            }}
                          />
                        </div>
                      </div>
                    ) : null}
                  </div>
                ) : null}
              </div>

              <div className="grid gap-3 sm:grid-cols-2">
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runSpec2RtlCheck} onChange={(e) => setRunSpec2RtlCheck(e.target.checked)} className="mt-1" />
                  <span>Run Spec2RTL conformance before implementation</span>
                </label>
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={enableScanDft} onChange={(e) => setEnableScanDft(e.target.checked)} className="mt-1" />
                  <span>Enable scan DFT and ATPG coverage evidence</span>
                </label>
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runFill} onChange={(e) => setRunFill(e.target.checked)} className="mt-1" />
                  <span>Run fill</span>
                </label>
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runDrc} onChange={(e) => setRunDrc(e.target.checked)} className="mt-1" />
                  <span>Run DRC</span>
                </label>
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/20 p-3 text-sm text-slate-300">
                  <input type="checkbox" checked={runLvs} onChange={(e) => setRunLvs(e.target.checked)} className="mt-1" />
                  <span>Run LVS</span>
                </label>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-2 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-amber-600 hover:bg-amber-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System PD"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

            </div>

            <div className="space-y-4">
              <div>
                <SpecTextBox label="Digital specification" required value={digitalSpecText} onChange={setDigitalSpecText} rows={6} voiceTitle="Digital Voice Spec" voiceLoopType="digital" voiceTarget="System digital spec" uploadLabel="Upload digital spec" uploadHelper="Digital behavior, interfaces, registers, and implementation-relevant requirements." placeholder="Paste digital spec here..." />
              </div>

              <div>
                <SpecTextBox label="Analog specification" required value={analogSpecText} onChange={setAnalogSpecText} rows={6} voiceTitle="Analog Voice Spec" voiceLoopType="analog" voiceTarget="System analog spec" uploadLabel="Upload analog spec" uploadHelper="Analog macro model, pins, observability, and physical assumptions." placeholder="Paste analog spec here..." />
              </div>

              <div>
                <SpecTextBox label="SoC integration specification" required value={socIntegrationSpecText} onChange={setSocIntegrationSpecText} rows={6} voiceTitle="SoC Voice Spec" voiceLoopType="system" voiceTarget="SoC integration spec" uploadLabel="Upload SoC integration spec" uploadHelper="Top-level integration, macro hookups, clock/reset/power assumptions, and system scenarios." placeholder="Paste SoC integration spec here..." />
              </div>
            </div>
          </div>

          {workflowId ? (
            <div className="mt-6 w-full rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
              <div>workflow_id: <span className="text-slate-100">{workflowId}</span></div>
              <div>run_id: <span className="text-slate-100">{runId}</span></div>
              <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                Download ZIP (full=1)
              </button>
              <div className="mt-4 rounded-xl border border-slate-800 bg-slate-950/70 p-3">
                <label className="text-xs font-semibold uppercase tracking-wide text-cyan-200">Run next workflow</label>
                <div className="mt-2 grid gap-2 sm:grid-cols-[1fr_auto]">
                  <select value={nextFlow} onChange={(e) => setNextFlow(e.target.value as typeof nextFlow)} className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-slate-100 outline-none focus:border-cyan-400">
                    <option value="system-firmware">System Firmware</option>
                  </select>
                  <button onClick={openNextFlow} className="rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500">Open</button>
                </div>
                <div className="mt-2 text-xs text-slate-400">
                  Source System RTL: <span className="break-all text-slate-200">{systemRtlWorkflowId.trim() || workflowId}</span>
                </div>
              </div>
              <div className="mt-4 w-full">
                <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="tapeout" logs={workflowRow?.logs} />
              </div>
              <div className="mt-4 w-full">
                <AskThisRunPanel workflowId={workflowId} compact />
              </div>
            </div>
          ) : null}

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
                <div className="text-slate-500">No logs yet. Click “Run System PD”.</div>
              )}
            </div>
          </div>

        </div>
      </div>
    </main>
  );
}

