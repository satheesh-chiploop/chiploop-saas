"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import SpecTextBox from "@/components/SpecTextBox";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  IMAGE_PRODUCT_INTENT,
  PRODUCT_BUILDER_PREFILL_KEY,
  PWM_PRODUCT_INTENT,
  SAFETY_PRODUCT_INTENT,
  SECURE_BOOT_PRODUCT_INTENT,
  SENSOR_PRODUCT_INTENT,
  UART_PRODUCT_INTENT,
  TEMP_MONITOR_SYSTEM_PRODUCT_INTENT,
  VALIDATION_HANDOFF_PREFILL_KEY,
  type DesignChainContext,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type ValidationMode = "software_package_validation" | "full_co_simulation";

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs
    .split("\n")
    .map((l) => l.trimEnd())
    .filter((l) => l.trim().length > 0);
}

function validationRunReady(row: WorkflowRow | null): boolean {
  if (!row) return false;
  const logs = row.logs || "";
  return (
    row.status === "completed" ||
    logs.includes("System Software Validation Summary Agent done") ||
    logs.includes("System Software Validation Summary (L2) done") ||
    logs.includes("System App complete: System_Software_Validation") ||
    logs.includes("validation_summary.json") ||
    logs.includes("cosim_validation_summary.json")
  );
}

export default function SystemSoftwareValidationAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  const [projectName, setProjectName] = useState("");
  const [validationMode, setValidationMode] =
    useState<ValidationMode>("software_package_validation");

  const [systemSoftwareWorkflowId, setSystemSoftwareWorkflowId] = useState("");
  const [systemFirmwareWorkflowId, setSystemFirmwareWorkflowId] = useState("");
  const [systemRtlWorkflowId, setSystemRtlWorkflowId] = useState("");
  const [goal, setGoal] = useState("");
  const [notes, setNotes] = useState("");
  const [handoffFlow, setHandoffFlow] = useState(false);
  const [pwmChainDemo, setPwmChainDemo] = useState(false);
  const [uartChainDemo, setUartChainDemo] = useState(false);
  const [imageChainDemo, setImageChainDemo] = useState(false);
  const [sensorChainDemo, setSensorChainDemo] = useState(false);
  const [secureChainDemo, setSecureChainDemo] = useState(false);
  const [safetyChainDemo, setSafetyChainDemo] = useState(false);
  const [tempMonitorChainDemo, setTempMonitorChainDemo] = useState(false);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const readyForProductBuilder = useMemo(() => validationRunReady(workflowRow), [workflowRow]);
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

  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/system-software-validation");
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
    if (params.get("handoff") !== "1" && params.get("pwm_chain") !== "1" && params.get("uart_chain") !== "1" && params.get("image_chain") !== "1" && params.get("sensor_chain") !== "1" && params.get("secure_chain") !== "1" && params.get("safety_chain") !== "1" && params.get("tempmon_chain") !== "1") return;
    setHandoffFlow(true);
    setPwmChainDemo(params.get("pwm_chain") === "1");
    setUartChainDemo(params.get("uart_chain") === "1");
    setImageChainDemo(params.get("image_chain") === "1");
    setSensorChainDemo(params.get("sensor_chain") === "1");
    setSecureChainDemo(params.get("secure_chain") === "1");
    setSafetyChainDemo(params.get("safety_chain") === "1");
    setTempMonitorChainDemo(params.get("tempmon_chain") === "1");
    const raw = window.localStorage.getItem(VALIDATION_HANDOFF_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as {
        projectName?: string;
        validationMode?: ValidationMode;
        systemSoftwareWorkflowId?: string;
        systemFirmwareWorkflowId?: string;
        systemRtlWorkflowId?: string;
        goal?: string;
        notes?: string;
      };
      setProjectName(prefill.projectName || "");
      setValidationMode(prefill.validationMode || "full_co_simulation");
      setSystemSoftwareWorkflowId(prefill.systemSoftwareWorkflowId || "");
      setSystemFirmwareWorkflowId(prefill.systemFirmwareWorkflowId || "");
      setSystemRtlWorkflowId(prefill.systemRtlWorkflowId || "");
      setGoal(prefill.goal || "");
      setNotes(prefill.notes || "");
    } catch {
      window.localStorage.removeItem(VALIDATION_HANDOFF_PREFILL_KEY);
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

      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        {
          event: "*",
          schema: "public",
          table: "workflows",
          filter: `id=eq.${workflowId}`,
        },
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

  const requiresFullCosimIds = validationMode === "full_co_simulation";

  const canRun = useMemo(() => {
    if (running) return false;
    if (!systemSoftwareWorkflowId.trim()) return false;
    if (requiresFullCosimIds && !systemFirmwareWorkflowId.trim()) return false;
    if (requiresFullCosimIds && !systemRtlWorkflowId.trim()) return false;
    return true;
  }, [
    running,
    requiresFullCosimIds,
    systemSoftwareWorkflowId,
    systemFirmwareWorkflowId,
    systemRtlWorkflowId,
  ]);

  async function runNow() {
    setErr(null);
    setRunning(true);

    try {
      const out = await postJSON<{
        ok: boolean;
        workflow_id: string;
        run_id: string;
        validation_mode: ValidationMode;
      }>("/apps/system/software-validation/run", {
        project_name: projectName || undefined,
        validation_mode: validationMode,
        system_software_workflow_id: systemSoftwareWorkflowId.trim(),
        system_firmware_workflow_id: requiresFullCosimIds
          ? systemFirmwareWorkflowId.trim()
          : undefined,
        system_rtl_workflow_id: requiresFullCosimIds
          ? systemRtlWorkflowId.trim()
          : undefined,
        goal: goal || undefined,
        notes: notes || undefined,
      });

      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
      const raw = window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY);
      let context: DesignChainContext = {};
      try {
        context = raw ? JSON.parse(raw) as DesignChainContext : {};
      } catch {
        context = {};
      }
      context.validationWorkflowId = out.workflow_id;
      context.validationRunId = out.run_id;
      context.demoKind = tempMonitorChainDemo ? "temp_monitor_system" : pwmChainDemo ? "pwm" : uartChainDemo ? "uart_packet" : imageChainDemo ? "image_dma" : sensorChainDemo ? "sensor_hub" : secureChainDemo ? "secure_boot" : safetyChainDemo ? "safety_fault" : context.demoKind;
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

  function openProductBuilder() {
    if (!workflowId) return;
    const raw = window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY);
    let context: DesignChainContext = {};
    try {
      context = raw ? JSON.parse(raw) as DesignChainContext : {};
    } catch {
      context = {};
    }
    context.validationWorkflowId = workflowId;
    context.validationRunId = runId || undefined;
    context.demoKind = tempMonitorChainDemo ? "temp_monitor_system" : pwmChainDemo ? "pwm" : uartChainDemo ? "uart_packet" : imageChainDemo ? "image_dma" : sensorChainDemo ? "sensor_hub" : secureChainDemo ? "secure_boot" : safetyChainDemo ? "safety_fault" : context.demoKind;
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    window.localStorage.setItem(PRODUCT_BUILDER_PREFILL_KEY, JSON.stringify({
      arch2rtlWorkflowId: context.systemRtlWorkflowId || context.arch2rtlWorkflowId || systemRtlWorkflowId,
      verifyWorkflowId: context.systemSimWorkflowId || context.verifyWorkflowId,
      systemFirmwareWorkflowId: context.systemFirmwareWorkflowId || context.embeddedWorkflowId || systemFirmwareWorkflowId,
      systemSoftwareWorkflowId: context.softwareWorkflowId || systemSoftwareWorkflowId,
      systemValidationWorkflowId: workflowId,
      productIntent: tempMonitorChainDemo ? TEMP_MONITOR_SYSTEM_PRODUCT_INTENT : pwmChainDemo ? PWM_PRODUCT_INTENT : uartChainDemo ? UART_PRODUCT_INTENT : imageChainDemo ? IMAGE_PRODUCT_INTENT : sensorChainDemo ? SENSOR_PRODUCT_INTENT : secureChainDemo ? SECURE_BOOT_PRODUCT_INTENT : safetyChainDemo ? SAFETY_PRODUCT_INTENT : "Build a simulator-backed product dashboard from the validated generated system collateral.",
      appType: "web_dashboard",
      targetRuntime: "simulated_device",
    }));
    router.push(`/apps/system-product-builder?handoff=1${tempMonitorChainDemo ? "&tempmon_chain=1" : ""}${pwmChainDemo ? "&pwm_chain=1" : ""}${uartChainDemo ? "&uart_chain=1" : ""}${imageChainDemo ? "&image_chain=1" : ""}${sensorChainDemo ? "&sensor_chain=1" : ""}${secureChainDemo ? "&secure_chain=1" : ""}${safetyChainDemo ? "&safety_chain=1" : ""}`);
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
          <button
            onClick={() => router.push("/apps")}
            className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
          >
            Back to Apps
          </button>
          <button
            onClick={() => router.push("/workflow")}
            className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900"
          >
            Studio
          </button>
        </div>

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">System Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-amber-300">
            System Software Validation
          </h1>
          <p className="mt-2 text-slate-300">
            Validate generated system software as either a software package-only
            flow or a full software → firmware → RTL co-simulation flow.
          </p>
          {pwmChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              PWM full-stack demo: validate the generated software, Rust firmware handoff, and imported PWM RTL together.
            </div>
          ) : uartChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              UART packet-engine demo: validate generated software, Rust firmware, and imported UART/FIFO RTL together.
            </div>
          ) : imageChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              Image DMA demo: validate generated image software, Rust firmware, and imported DMA/filter/histogram RTL together.
            </div>
          ) : sensorChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              Smart sensor hub demo: validate generated IoT telemetry software, Rust firmware, and imported sensor hub RTL together.
            </div>
          ) : secureChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              Secure boot demo: validate generated provisioning/status software, Rust firmware, and imported root-of-trust RTL together.
            </div>
          ) : safetyChainDemo ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              Safety fault demo: validate generated safety monitor software, Rust firmware, and imported watchdog/fault RTL together.
            </div>
          ) : handoffFlow ? (
            <div className="mt-4 rounded-xl border border-amber-800/60 bg-amber-950/20 p-4 text-sm text-slate-200">
              Imported full-stack handoff: validate the generated software, firmware, and original Arch2RTL hardware together.
            </div>
          ) : null}

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-4">
              <div>
                <label className="block text-sm text-slate-300">
                  Project name (optional)
                </label>
                <input
                  value={projectName}
                  onChange={(e) => setProjectName(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="System software validation"
                />
              </div>

              <div>
                <label className="block text-sm text-slate-300">Validation mode *</label>
                <div className="mt-2 grid grid-cols-1 gap-3 sm:grid-cols-2">
                  <button
                    type="button"
                    onClick={() => setValidationMode("software_package_validation")}
                    className={`rounded-2xl border px-4 py-4 text-left transition ${
                      validationMode === "software_package_validation"
                        ? "border-amber-400 bg-amber-500/10"
                        : "border-slate-800 bg-black/20 hover:bg-slate-900"
                    }`}
                  >
                    <div className="font-semibold text-slate-100">
                      Software Package Validation
                    </div>
                    <div className="mt-1 text-sm text-slate-400">
                      Validate build, tests, contracts, mock runtime, and package completeness.
                    </div>
                  </button>

                  <button
                    type="button"
                    onClick={() => setValidationMode("full_co_simulation")}
                    className={`rounded-2xl border px-4 py-4 text-left transition ${
                      validationMode === "full_co_simulation"
                        ? "border-amber-400 bg-amber-500/10"
                        : "border-slate-800 bg-black/20 hover:bg-slate-900"
                    }`}
                  >
                    <div className="font-semibold text-slate-100">
                      Full Co-Simulation
                    </div>
                    <div className="mt-1 text-sm text-slate-400">
                      Validate software → firmware → RTL behavior across integrated scenarios.
                    </div>
                  </button>
                </div>
              </div>

              <div>
                <label className="block text-sm text-slate-300">
                  System software workflow ID *
                </label>
                <input
                  value={systemSoftwareWorkflowId}
                  onChange={(e) => setSystemSoftwareWorkflowId(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                  placeholder="Enter System_Software workflow id"
                />
              </div>

              {requiresFullCosimIds ? (
                <>
                  <div>
                    <label className="block text-sm text-slate-300">
                      System firmware workflow ID *
                    </label>
                    <input
                      value={systemFirmwareWorkflowId}
                      onChange={(e) => setSystemFirmwareWorkflowId(e.target.value)}
                      className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                      placeholder="Required for full co-simulation"
                    />
                  </div>

                  <div>
                    <label className="block text-sm text-slate-300">
                      System RTL workflow ID *
                    </label>
                    <input
                      value={systemRtlWorkflowId}
                      onChange={(e) => setSystemRtlWorkflowId(e.target.value)}
                      className="mt-2 w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100"
                      placeholder="Required for full co-simulation"
                    />
                  </div>
                </>
              ) : null}

              <div>
                <SpecTextBox
                  label="Goal (optional)"
                  value={goal}
                  onChange={setGoal}
                  rows={3}
                  voiceTitle="Validation Goal Voice Spec"
                  voiceLoopType="validation"
                  voiceTarget="System Software Validation goal"
                  uploadLabel="Upload validation goal"
                  uploadHelper="Load validation requirements, scenarios, markdown, JSON, YAML, logs, or text notes."
                  placeholder="What do you want to prove with this validation run?"
                />
              </div>

              <div>
                <label className="block text-sm text-slate-300">Notes (optional)</label>
                <textarea
                  value={notes}
                  onChange={(e) => setNotes(e.target.value)}
                  rows={4}
                  className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                  placeholder="Optional run notes, assumptions, scenario focus, or debug intent."
                />
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun
                    ? "bg-amber-600 hover:bg-amber-500"
                    : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting…" : "Run System Software Validation"}
              </button>

              {err ? <div className="text-sm text-red-300">{err}</div> : null}

              {workflowId ? (
                <div className="rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>
                    workflow_id: <span className="text-slate-100">{workflowId}</span>
                  </div>
                  <div>
                    run_id: <span className="text-slate-100">{runId}</span>
                  </div>
                  <button
                    onClick={downloadZip}
                    className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
                  >
                    Download ZIP (full=1)
                  </button>
                  <button
                    onClick={openProductBuilder}
                    disabled={!readyForProductBuilder}
                    className="ml-3 mt-3 rounded-xl bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    Build Product App
                  </button>
                  {pwmChainDemo ? (
                    <div className="mt-4">
                      <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="validation" logs={workflowRow?.logs} />
                    </div>
                  ) : null}
                    <AskThisRunPanel workflowId={workflowId} compact />
                </div>
              ) : null}
            </div>

            <div className="space-y-4">
              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-100">What this app does</div>
                <ul className="mt-3 space-y-2 text-sm text-slate-300">
                  <li>• Restores required artifacts from previous workflow outputs.</li>
                  <li>• Runs software-only validation or full-stack co-simulation validation.</li>
                  <li>• Streams workflow logs live from the backend.</li>
                  <li>• Produces a downloadable ZIP of validation artifacts.</li>
                </ul>
              </div>

              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-100">Required inputs</div>
                <div className="mt-3 text-sm text-slate-300">
                  {requiresFullCosimIds ? (
                    <ul className="space-y-2">
                      <li>• System software workflow ID</li>
                      <li>• System firmware workflow ID</li>
                      <li>• System RTL workflow ID</li>
                    </ul>
                  ) : (
                    <ul className="space-y-2">
                      <li>• System software workflow ID</li>
                    </ul>
                  )}
                </div>
              </div>

              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-sm font-semibold text-slate-100">Validation outputs</div>
                <div className="mt-3 text-sm text-slate-300">
                  {requiresFullCosimIds ? (
                    <ul className="space-y-2">
                      <li>• Co-simulation harness + execution evidence</li>
                      <li>• Cross-layer trace / mismatch reports</li>
                      <li>• Full-stack readiness summary</li>
                    </ul>
                  ) : (
                    <ul className="space-y-2">
                      <li>• Build validation report</li>
                      <li>• Test execution report</li>
                      <li>• Contract consistency report</li>
                      <li>• Package audit + validation summary</li>
                    </ul>
                  )}
                </div>
              </div>

              <div className="rounded-2xl border border-slate-800 bg-black/20 p-4">
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
                    <div className="text-slate-500">
                      No logs yet. Click “Run System Software Validation”.
                    </div>
                  )}
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}
