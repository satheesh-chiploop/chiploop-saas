"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import {
  PRODUCT_BUILDER_PREFILL_KEY,
  type DesignChainContext,
  DESIGN_CHAIN_CONTEXT_KEY,
} from "@/lib/pwmFullStackDemo";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

type WorkflowRow = { id: string; status?: string | null; phase?: string | null; logs?: string | null };

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter(Boolean);
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

  const [arch2rtlWorkflowId, setArch2rtlWorkflowId] = useState("");
  const [verifyWorkflowId, setVerifyWorkflowId] = useState("");
  const [systemFirmwareWorkflowId, setSystemFirmwareWorkflowId] = useState("");
  const [systemSoftwareWorkflowId, setSystemSoftwareWorkflowId] = useState("");
  const [systemValidationWorkflowId, setSystemValidationWorkflowId] = useState("");
  const [productIntent, setProductIntent] = useState("");
  const [appType, setAppType] = useState("web_dashboard");
  const [targetRuntime, setTargetRuntime] = useState("simulated_device");

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
      setArch2rtlWorkflowId(prefill.arch2rtlWorkflowId || context.arch2rtlWorkflowId || "");
      setVerifyWorkflowId(prefill.verifyWorkflowId || context.verifyWorkflowId || "");
      setSystemFirmwareWorkflowId(prefill.systemFirmwareWorkflowId || context.embeddedWorkflowId || "");
      setSystemSoftwareWorkflowId(prefill.systemSoftwareWorkflowId || context.softwareWorkflowId || "");
      setSystemValidationWorkflowId(prefill.systemValidationWorkflowId || context.validationWorkflowId || "");
      setProductIntent(prefill.productIntent || "Build a simulator-backed product dashboard from the validated system collateral.");
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
          {pwmChainDemo ? (
            <div className="mt-4 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-4 text-sm text-slate-200">
              PWM full-stack demo: build a live fan-control dashboard driven by generated workflow lineage.
            </div>
          ) : null}

          <div className="mt-6 grid gap-5 lg:grid-cols-[minmax(0,0.95fr)_minmax(420px,0.85fr)]">
            <div className="space-y-4">
              <div className="grid gap-3 sm:grid-cols-2">
                <input value={arch2rtlWorkflowId} onChange={(e) => setArch2rtlWorkflowId(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Arch2RTL workflow ID" />
                <input value={verifyWorkflowId} onChange={(e) => setVerifyWorkflowId(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Verify workflow ID" />
                <input value={systemFirmwareWorkflowId} onChange={(e) => setSystemFirmwareWorkflowId(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Firmware workflow ID" />
                <input value={systemSoftwareWorkflowId} onChange={(e) => setSystemSoftwareWorkflowId(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" placeholder="Software workflow ID *" />
                <input value={systemValidationWorkflowId} onChange={(e) => setSystemValidationWorkflowId(e.target.value)} className="rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100 sm:col-span-2" placeholder="Validation workflow ID *" />
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
                  <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Download Product ZIP</button>
                </div>
              ) : null}
              {workflowId ? <AskThisRunPanel workflowId={workflowId} compact /> : null}
            </div>
          </div>

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
