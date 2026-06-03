"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import VoiceSpecDraft from "@/components/VoiceSpecDraft";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  EMBEDDED_HANDOFF_PREFILL_KEY,
  GENERIC_SOFTWARE_GOAL,
  IMAGE_SOFTWARE_GOAL,
  PWM_SOFTWARE_GOAL,
  SAFETY_SOFTWARE_GOAL,
  SECURE_BOOT_SOFTWARE_GOAL,
  SENSOR_SOFTWARE_GOAL,
  UART_SOFTWARE_GOAL,
  SOFTWARE_HANDOFF_PREFILL_KEY,
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

type Props = {
  title: string;
  subtitle: string;
  runPath: string; // e.g. "/apps/embedded/hal/run"
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter((line) => line.trim().length > 0);
}

export default function EmbeddedAppTemplate({ title, subtitle, runPath }: Props) {
  const router = useRouter();

  const [loading, setLoading] = useState(true);
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [specText, setSpecText] = useState("");
  const [goal, setGoal] = useState("");
  const [handoffFlow, setHandoffFlow] = useState(false);
  const [pwmChainDemo, setPwmChainDemo] = useState(false);
  const [uartChainDemo, setUartChainDemo] = useState(false);
  const [imageChainDemo, setImageChainDemo] = useState(false);
  const [sensorChainDemo, setSensorChainDemo] = useState(false);
  const [secureChainDemo, setSecureChainDemo] = useState(false);
  const [safetyChainDemo, setSafetyChainDemo] = useState(false);
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [fromRunId, setFromRunId] = useState("");
  const [sourceVerificationWorkflowId, setSourceVerificationWorkflowId] = useState("");
  const [sourceVerificationRunId, setSourceVerificationRunId] = useState("");
  const [topModule, setTopModule] = useState("");

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
  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const embeddedReady = useMemo(() => {
    const status = String(workflowRow?.status || "").trim().toLowerCase();
    if (["completed", "complete", "success", "succeeded"].includes(status)) return true;
    return logLines.some((line) =>
      line.includes("System Software Handoff Package Agent done") ||
      line.includes("Embedded App complete")
    );
  }, [logLines, workflowRow?.status]);

  function authHeaders(): Record<string, string> {
    const headers: Record<string, string> = {};
    if (sessionUserId) headers["x-user-id"] = sessionUserId;
    if (accessToken) headers["Authorization"] = `Bearer ${accessToken}`;
    return headers;
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
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        router.replace("/login?next=/apps/embedded-run");
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
    if (params.get("handoff") !== "1" && params.get("pwm_chain") !== "1" && params.get("uart_chain") !== "1" && params.get("image_chain") !== "1" && params.get("sensor_chain") !== "1" && params.get("secure_chain") !== "1" && params.get("safety_chain") !== "1") return;
    setHandoffFlow(true);
    setPwmChainDemo(params.get("pwm_chain") === "1");
    setUartChainDemo(params.get("uart_chain") === "1");
    setImageChainDemo(params.get("image_chain") === "1");
    setSensorChainDemo(params.get("sensor_chain") === "1");
    setSecureChainDemo(params.get("secure_chain") === "1");
    setSafetyChainDemo(params.get("safety_chain") === "1");
    const raw = window.localStorage.getItem(EMBEDDED_HANDOFF_PREFILL_KEY);
    if (!raw) return;
    try {
      const prefill = JSON.parse(raw) as {
        specText?: string;
        goal?: string;
        fromWorkflowId?: string;
        fromRunId?: string;
        sourceVerificationWorkflowId?: string;
        sourceVerificationRunId?: string;
        topModule?: string;
      };
      setSpecText(prefill.specText || "");
      setGoal(prefill.goal || "");
      setFromWorkflowId(prefill.fromWorkflowId || "");
      setFromRunId(prefill.fromRunId || "");
      setSourceVerificationWorkflowId(prefill.sourceVerificationWorkflowId || "");
      setSourceVerificationRunId(prefill.sourceVerificationRunId || "");
      setTopModule(prefill.topModule || "pwm_controller");
    } catch {
      window.localStorage.removeItem(EMBEDDED_HANDOFF_PREFILL_KEY);
    }
  }, [loading]);

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
    if (handoffFlow && (!fromWorkflowId.trim() || !sourceVerificationWorkflowId.trim())) return false;
    return specText.trim().length > 0;
  }, [running, specText, handoffFlow, fromWorkflowId, sourceVerificationWorkflowId]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(runPath, {
        spec_text: specText,
        goal: goal || undefined,
        toolchain,
        toggles,
        from_workflow_id: fromWorkflowId || undefined,
        from_run_id: fromRunId || undefined,
        source_verification_workflow_id: sourceVerificationWorkflowId || undefined,
        source_verification_run_id: sourceVerificationRunId || undefined,
        top_module: topModule || undefined,
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

  function openInSystemSoftware() {
    if (!workflowId) return;
    let context: DesignChainContext = {};
    try {
      context = JSON.parse(window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY) || "{}") as DesignChainContext;
    } catch {
      context = {};
    }
    context.embeddedWorkflowId = workflowId;
    context.embeddedRunId = runId || undefined;
    context.demoKind = pwmChainDemo ? "pwm" : uartChainDemo ? "uart_packet" : imageChainDemo ? "image_dma" : sensorChainDemo ? "sensor_hub" : secureChainDemo ? "secure_boot" : safetyChainDemo ? "safety_fault" : context.demoKind;
    const sourceRtlWorkflowId = context.arch2rtlWorkflowId || fromWorkflowId || "";
    window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
    window.localStorage.setItem(SOFTWARE_HANDOFF_PREFILL_KEY, JSON.stringify({
      projectName: pwmChainDemo ? "pwm_fan_control_software" : uartChainDemo ? "uart_packet_engine_software" : imageChainDemo ? "image_dma_pipeline_software" : sensorChainDemo ? "smart_sensor_hub_software" : secureChainDemo ? "secure_boot_software" : safetyChainDemo ? "safety_fault_watchdog_software" : "generated_hardware_software",
      systemFirmwareWorkflowId: workflowId,
      systemRtlWorkflowId: sourceRtlWorkflowId,
      softwareGoal: pwmChainDemo ? PWM_SOFTWARE_GOAL : uartChainDemo ? UART_SOFTWARE_GOAL : imageChainDemo ? IMAGE_SOFTWARE_GOAL : sensorChainDemo ? SENSOR_SOFTWARE_GOAL : secureChainDemo ? SECURE_BOOT_SOFTWARE_GOAL : safetyChainDemo ? SAFETY_SOFTWARE_GOAL : GENERIC_SOFTWARE_GOAL,
      appNames: pwmChainDemo ? "fan_status_cli, fan_profile_service" : uartChainDemo ? "uart_packet_cli, telemetry_packet_service" : imageChainDemo ? "image_pipeline_cli, frame_processing_service" : sensorChainDemo ? "sensor_node_cli, telemetry_alert_service" : secureChainDemo ? "secure_boot_cli, provisioning_status_service" : safetyChainDemo ? "safety_health_cli, watchdog_monitor_service" : "",
      targetLanguage: "rust",
      sdkStyle: "rust_crate",
      buildSystem: "cargo",
      notes: "Source RTL and interface artifacts were imported from Arch2RTL; verification lineage is preserved in the firmware handoff.",
    }));
    router.push(`/apps/system-software?handoff=1${pwmChainDemo ? "&pwm_chain=1" : ""}${uartChainDemo ? "&uart_chain=1" : ""}${imageChainDemo ? "&image_chain=1" : ""}${sensorChainDemo ? "&sensor_chain=1" : ""}${secureChainDemo ? "&secure_chain=1" : ""}${safetyChainDemo ? "&safety_chain=1" : ""}`);
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
            <span className="text-cyan-400">ChipLoop</span>
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
          {pwmChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              PWM full-stack demo: this run imports the generated PWM RTL and register map, then creates Rust fan-control firmware collateral against that hardware interface.
            </div>
          ) : uartChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              UART packet-engine demo: this run imports UART/FIFO/register collateral, then creates Rust firmware for packet send/receive, IRQ handling, and error status.
            </div>
          ) : imageChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Image DMA demo: this run imports image pipeline registers, DMA controls, filter settings, histogram counters, and frame-status collateral.
            </div>
          ) : sensorChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Smart sensor hub demo: this run imports sensor telemetry, FIFO, threshold alert, interrupt, and low-power registers, then creates Rust IoT firmware collateral.
            </div>
          ) : secureChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Secure boot demo: this run imports boot authentication, key manager, rollback, tamper, debug-lock, and audit registers, then creates Rust security firmware collateral.
            </div>
          ) : safetyChainDemo ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Safety fault demo: this run imports watchdog, fault, escalation, reset request, and safety IRQ registers, then creates Rust safety firmware collateral.
            </div>
          ) : handoffFlow ? (
            <div className="mt-4 rounded-xl border border-emerald-900/60 bg-emerald-950/20 p-4 text-sm text-slate-200">
              Imported hardware handoff: this run uses generated RTL and register-map artifacts from the selected Arch2RTL workflow.
            </div>
          ) : null}
          {handoffFlow ? (
            <div className="mt-4 grid gap-3 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm md:grid-cols-2">
              <div>
                <label className="block text-xs text-slate-400">Arch2RTL source workflow ID</label>
                <input
                  value={fromWorkflowId}
                  onChange={(e) => setFromWorkflowId(e.target.value)}
                  className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-slate-100"
                  placeholder="Required Arch2RTL workflow ID"
                />
              </div>
              <div>
                <label className="block text-xs text-slate-400">Verify evidence workflow ID</label>
                <input
                  value={sourceVerificationWorkflowId}
                  onChange={(e) => setSourceVerificationWorkflowId(e.target.value)}
                  className="mt-1 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-slate-100"
                  placeholder="Required Verify workflow ID"
                />
              </div>
              <div className="text-xs text-slate-400">
                Arch2RTL run ID: <span className="text-slate-200">{fromRunId || "not recorded"}</span>
              </div>
              <div className="text-xs text-slate-400">
                Verify run ID: <span className="text-slate-200">{sourceVerificationRunId || "not recorded"}</span>
              </div>
            </div>
          ) : null}
        </div>

        {/* One-shot intake */}
        <div className="grid grid-cols-1 gap-6 lg:grid-cols-2">
          <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-6 space-y-4">
            <div className="text-lg font-bold">One-shot input</div>
            <VoiceSpecDraft title="Voice Spec Draft" loopType="embedded" target="Embedded App spec" onApply={setSpecText} />


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
            {workflowId ? <AskThisRunPanel workflowId={workflowId} compact /> : null}
            {workflowId && handoffFlow && runPath === "/apps/embedded/run" ? (
              <button
                type="button"
                onClick={openInSystemSoftware}
                disabled={!embeddedReady}
                className="rounded-xl bg-cyan-700 px-4 py-2 text-sm font-semibold hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-400"
              >
                Open in System Software
              </button>
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

        {pwmChainDemo && workflowId ? (
          <WorkflowEvidenceDashboard workflowId={workflowId} status={embeddedReady ? "completed" : workflowRow?.status} stage="embedded" logs={workflowRow?.logs} />
        ) : null}

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
