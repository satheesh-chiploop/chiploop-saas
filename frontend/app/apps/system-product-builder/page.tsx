"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  IMAGE_PRODUCT_INTENT,
  PRODUCT_BUILDER_PREFILL_KEY,
  PWM_PRODUCT_INTENT,
  SAFETY_PRODUCT_INTENT,
  SECURE_BOOT_PRODUCT_INTENT,
  SENSOR_PRODUCT_INTENT,
  TEMP_MONITOR_SYSTEM_PRODUCT_INTENT,
  UART_PRODUCT_INTENT,
  type DesignChainContext,
  DESIGN_CHAIN_CONTEXT_KEY,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = { id: string; status?: string | null; phase?: string | null; logs?: string | null };

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter(Boolean);
}

function countParticipatingAgents(logs: string | null | undefined): number | null {
  if (!logs) return null;
  const agents = new Set<string>();
  for (const rawLine of logs.split("\n")) {
    const line = rawLine.trim();
    const running = line.match(/Running\s+(.+?\sAgent)\b/i);
    const finished = line.match(/^(.+?\sAgent)\s+(?:done|failed)\b/i);
    const name = running?.[1] || finished?.[1];
    if (name) agents.add(name.trim());
  }
  return agents.size || null;
}

function productIntentForContext(demoKind: unknown): string {
  const kind = String(demoKind || "").toLowerCase();
  if (kind.includes("temp_monitor")) return TEMP_MONITOR_SYSTEM_PRODUCT_INTENT;
  if (kind.includes("sram") || kind.includes("mbist")) {
    return "Build a simulator-backed SRAM scratchpad controller dashboard with memory read/write controls, MBIST start/status, IRQ visibility, and validation lineage.";
  }
  if (kind.includes("pwm")) return PWM_PRODUCT_INTENT;
  if (kind.includes("uart")) return UART_PRODUCT_INTENT;
  if (kind.includes("image")) return IMAGE_PRODUCT_INTENT;
  if (kind.includes("sensor")) return SENSOR_PRODUCT_INTENT;
  if (kind.includes("secure")) return SECURE_BOOT_PRODUCT_INTENT;
  if (kind.includes("safety")) return SAFETY_PRODUCT_INTENT;
  return "Build a simulator-backed product dashboard from the validated system collateral.";
}

function WorkflowIdField({
  label,
  helper,
  value,
  onChange,
  required = false,
}: {
  label: string;
  helper: string;
  value: string;
  onChange: (value: string) => void;
  required?: boolean;
}) {
  return (
    <label className="block rounded-xl border border-slate-800 bg-black/20 p-3">
      <span className="block text-xs font-semibold uppercase tracking-wide text-cyan-200">
        {label}{required ? " *" : ""}
      </span>
      <span className="mt-1 block text-xs text-slate-500">{helper}</span>
      <input
        value={value}
        onChange={(e) => onChange(e.target.value)}
        className="mt-2 w-full rounded-lg border border-slate-800 bg-black/30 px-3 py-2 text-slate-100"
        placeholder={`${label} workflow ID`}
      />
    </label>
  );
}

export default function SystemProductBuilderPage() {
  const router = useRouter();
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [pwmChainDemo, setPwmChainDemo] = useState(false);
  const [uartChainDemo, setUartChainDemo] = useState(false);
  const [imageChainDemo, setImageChainDemo] = useState(false);
  const [sensorChainDemo, setSensorChainDemo] = useState(false);
  const [secureChainDemo, setSecureChainDemo] = useState(false);
  const [safetyChainDemo, setSafetyChainDemo] = useState(false);
  const [tempMonitorChainDemo, setTempMonitorChainDemo] = useState(false);
  const [sramChainDemo, setSramChainDemo] = useState(false);

  const [arch2rtlWorkflowId, setArch2rtlWorkflowId] = useState("");
  const [verifyWorkflowId, setVerifyWorkflowId] = useState("");
  const [systemFirmwareWorkflowId, setSystemFirmwareWorkflowId] = useState("");
  const [systemSoftwareWorkflowId, setSystemSoftwareWorkflowId] = useState("");
  const [systemValidationWorkflowId, setSystemValidationWorkflowId] = useState("");
  const [productIntent, setProductIntent] = useState("");
  const [appType, setAppType] = useState("web_dashboard");
  const [targetRuntime, setTargetRuntime] = useState("simulated_device");

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const agentCount = useMemo(() => countParticipatingAgents(workflowRow?.logs), [workflowRow?.logs]);
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
    const text = await resp.text().catch(() => "");
    if (!resp.ok) throw new Error(`${resp.status} ${resp.statusText}${text ? ` - ${text}` : ""}`);
    return JSON.parse(text) as T;
  }

  useEffect(() => {
    (async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/system-product-builder");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    setPwmChainDemo(params.get("pwm_chain") === "1");
    setUartChainDemo(params.get("uart_chain") === "1");
    setImageChainDemo(params.get("image_chain") === "1");
    setSensorChainDemo(params.get("sensor_chain") === "1");
    setSecureChainDemo(params.get("secure_chain") === "1");
    setSafetyChainDemo(params.get("safety_chain") === "1");
    setTempMonitorChainDemo(params.get("tempmon_chain") === "1");
    const rawPrefill = window.localStorage.getItem(PRODUCT_BUILDER_PREFILL_KEY);
    const rawContext = window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY);
    let context: DesignChainContext = {};
    try {
      context = rawContext ? JSON.parse(rawContext) as DesignChainContext : {};
    } catch {
      context = {};
    }
    try {
      const prefill = rawPrefill ? JSON.parse(rawPrefill) as any : {};
      const isTempMonitor = params.get("tempmon_chain") === "1";
      const isSram = params.get("sram_chain") === "1" || String(context.demoKind || "").toLowerCase().includes("sram");
      setSramChainDemo(isSram);
      setArch2rtlWorkflowId(prefill.arch2rtlWorkflowId || context.systemRtlWorkflowId || context.arch2rtlWorkflowId || "");
      setVerifyWorkflowId(prefill.verifyWorkflowId || context.systemSimWorkflowId || context.verifyWorkflowId || "");
      setSystemFirmwareWorkflowId(prefill.systemFirmwareWorkflowId || context.systemFirmwareWorkflowId || context.embeddedWorkflowId || "");
      setSystemSoftwareWorkflowId(prefill.systemSoftwareWorkflowId || context.softwareWorkflowId || "");
      setSystemValidationWorkflowId(prefill.systemValidationWorkflowId || context.validationWorkflowId || "");
      setProductIntent(prefill.productIntent || productIntentForContext(isTempMonitor ? "temp_monitor_system" : isSram ? "mbist_sram" : context.demoKind));
      setAppType(prefill.appType || "web_dashboard");
      setTargetRuntime(prefill.targetRuntime || "simulated_device");
    } catch {
      window.localStorage.removeItem(PRODUCT_BUILDER_PREFILL_KEY);
    }
  }, [loading]);

  useEffect(() => {
    if (!workflowId) return;
    let active = true;
    const fetchWorkflow = async () => {
      const { data, error } = await supabase.from("workflows").select("id,status,phase,logs").eq("id", workflowId).single();
      if (active && !error && data) setWorkflowRow(data as WorkflowRow);
    };
    void fetchWorkflow();
    const interval = window.setInterval(() => void fetchWorkflow(), 2500);
    const channel = supabase.channel(`wf-${workflowId}`).on(
      "postgres_changes",
      { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
      (payload) => setWorkflowRow(payload.new as WorkflowRow),
    ).subscribe();
    return () => {
      active = false;
      window.clearInterval(interval);
      supabase.removeChannel(channel);
    };
  }, [workflowId]);

  const canRun = useMemo(() => {
    if (running) return false;
    return Boolean(systemSoftwareWorkflowId.trim() && systemValidationWorkflowId.trim() && productIntent.trim());
  }, [running, systemSoftwareWorkflowId, systemValidationWorkflowId, productIntent]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/system/product-builder/run", {
        arch2rtl_workflow_id: arch2rtlWorkflowId || undefined,
        verify_workflow_id: verifyWorkflowId || undefined,
        system_firmware_workflow_id: systemFirmwareWorkflowId || undefined,
        system_software_workflow_id: systemSoftwareWorkflowId,
        system_validation_workflow_id: systemValidationWorkflowId,
        product_intent: productIntent,
        app_type: appType,
        target_runtime: targetRuntime,
      });
      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
      const raw = window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY);
      let context: DesignChainContext = {};
      try { context = raw ? JSON.parse(raw) as DesignChainContext : {}; } catch { context = {}; }
      context.productWorkflowId = out.workflow_id;
      context.productRunId = out.run_id;
      context.demoKind = tempMonitorChainDemo ? "temp_monitor_system" : sramChainDemo ? "sram_mbist" : pwmChainDemo ? "pwm" : uartChainDemo ? "uart_packet" : imageChainDemo ? "image_dma" : sensorChainDemo ? "sensor_hub" : secureChainDemo ? "secure_boot" : safetyChainDemo ? "safety_fault" : context.demoKind;
      window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
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
    return <main className="flex min-h-screen items-center justify-center bg-black text-white">Loading...</main>;
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-6xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Back to Apps</button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">Studio</button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Product App Builder</h1>
          <p className="mt-2 text-slate-300">
            Generate a simulator-backed product interface from validated RTL, firmware, software, and validation collateral.
          </p>
          {tempMonitorChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Temperature monitor SoC journey: build a simulator-backed product dashboard from System RTL, System Sim, firmware, software, and validation lineage.
            </div>
          ) : sramChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              SRAM MBIST demo: build a simulator-backed scratchpad controller dashboard for memory read/write, MBIST start/status, IRQ state, and validation lineage.
            </div>
          ) : pwmChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              PWM full-stack demo: build a live fan-control dashboard driven by generated workflow lineage.
            </div>
          ) : uartChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              UART packet-engine demo: build a simulator-backed dashboard for baud setup, packet movement, FIFO levels, IRQ status, and error scenarios.
            </div>
          ) : imageChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Image DMA demo: build a simulator-backed dashboard for filter controls, DMA progress, input/output preview, histogram, and interrupt status.
            </div>
          ) : sensorChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Smart sensor hub demo: build a simulator-backed IoT dashboard for sample rate, sensor channels, live telemetry, FIFO depth, alerts, and low-power state.
            </div>
          ) : secureChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Secure boot demo: build a simulator-backed security dashboard for key slots, boot authentication, rollback, tamper, debug lock, IRQ, and audit state.
            </div>
          ) : safetyChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              Safety fault demo: build a simulator-backed safety dashboard for watchdog, heartbeat, fault injection, escalation, reset request, and safety IRQ state.
            </div>
          ) : null}

          <div className="mt-6 grid gap-5 lg:grid-cols-[minmax(0,0.95fr)_minmax(420px,0.85fr)]">
            <div className="space-y-4">
              <div className="grid gap-3 sm:grid-cols-2">
                <WorkflowIdField
                  label="RTL source"
                  helper="System RTL or Digital_Arch2RTL run that generated RTL, register map, constraints, and handoff collateral."
                  value={arch2rtlWorkflowId}
                  onChange={setArch2rtlWorkflowId}
                />
                <WorkflowIdField
                  label="Verification evidence"
                  helper="System Sim or Digital_Verify run with simulation, coverage, assertions, formal, and debug evidence."
                  value={verifyWorkflowId}
                  onChange={setVerifyWorkflowId}
                />
                <WorkflowIdField
                  label="Firmware handoff"
                  helper="Embedded_Run or firmware workflow that generated drivers, register access, and co-sim collateral."
                  value={systemFirmwareWorkflowId}
                  onChange={setSystemFirmwareWorkflowId}
                />
                <WorkflowIdField
                  label="Software package"
                  helper="System_Software run that generated SDK, API contract, service, app, and package artifacts."
                  value={systemSoftwareWorkflowId}
                  onChange={setSystemSoftwareWorkflowId}
                  required
                />
                <div className="sm:col-span-2">
                  <WorkflowIdField
                    label="Validation evidence"
                    helper="System_Software_Validation run proving software to firmware to RTL behavior across scenarios."
                    value={systemValidationWorkflowId}
                    onChange={setSystemValidationWorkflowId}
                    required
                  />
                </div>
              </div>
              <textarea value={productIntent} onChange={(e) => setProductIntent(e.target.value)} rows={6} className="w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100" placeholder="Describe the product interface to generate." />
              <div className="grid gap-3 sm:grid-cols-2">
                <select value={appType} onChange={(e) => setAppType(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                  <option value="web_dashboard">Web dashboard</option>
                  <option value="cli_tool" disabled>CLI tool (planned)</option>
                </select>
                <select value={targetRuntime} onChange={(e) => setTargetRuntime(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                  <option value="simulated_device">Simulated device</option>
                  <option value="board_transport" disabled>Board transport (planned)</option>
                </select>
              </div>
              <button onClick={runNow} disabled={!canRun} className={`w-full rounded-xl px-5 py-3 font-semibold transition ${canRun ? "bg-cyan-600 hover:bg-cyan-500" : "cursor-not-allowed bg-slate-700"}`}>
                {running ? "Starting..." : "Build Product App"}
              </button>
              {err ? <div className="text-sm text-red-300">{err}</div> : null}
            </div>

            <div className="space-y-4">
              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4 text-sm text-slate-300">
                <div className="font-semibold text-slate-100">Output</div>
                <div className="mt-2">Download the ZIP and open <span className="text-cyan-200">system/product/app/index.html</span>.</div>
                <div className="mt-2">The simulator adapter can later be replaced by UART, JTAG, Ethernet, or board transport.</div>
              </div>
              {workflowId ? (
                <div className="rounded-2xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>workflow_id: <span className="break-all text-slate-100">{workflowId}</span></div>
                  <div>run_id: <span className="break-all text-slate-100">{runId}</span></div>
                  <div>status: <span className="text-slate-100">{workflowRow?.status || "queued"}</span></div>
                  {agentCount !== null ? <div>agents participated: <span className="text-slate-100">{agentCount}</span></div> : null}
                  <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Download Product ZIP</button>
                </div>
              ) : null}
              {workflowId ? <AskThisRunPanel workflowId={workflowId} compact /> : null}
            </div>
          </div>
          {workflowId ? (
            <div className="mt-6">
              <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="product" logs={workflowRow?.logs} />
            </div>
          ) : null}

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((line, index) => <div key={index} className="whitespace-pre-wrap">{line}</div>) : <div className="text-slate-500">No logs yet. Click Build Product App.</div>}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
