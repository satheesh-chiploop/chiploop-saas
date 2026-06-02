"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  GENERIC_VERIFY_INTENT,
  VERIFY_HANDOFF_PREFILL_KEY,
  type DesignChainContext,
} from "@/lib/pwmFullStackDemo";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";

type ChainStage = "arch2rtl" | "dqa" | "smoke" | "synthesis" | "tapeout" | "verify";
type NextAction = "verify" | "dqa" | "smoke" | "synthesis" | "tapeout";

type StartedRun = {
  action: NextAction;
  workflowId: string;
  runId?: string | null;
};

const ACTION_LABELS: Record<NextAction, string> = {
  verify: "Verification",
  dqa: "DQA checks",
  smoke: "Smoke simulation",
  synthesis: "Synthesis",
  tapeout: "Tapeout prep",
};

const ACTION_ENDPOINTS: Record<Exclude<NextAction, "verify">, string> = {
  dqa: "/apps/dqa/run",
  smoke: "/apps/smoke/run",
  synthesis: "/apps/arch2synthesis/run",
  tapeout: "/apps/arch2tapeout/run",
};

function optionsForStage(stage: ChainStage): NextAction[] {
  if (stage === "arch2rtl") return ["verify", "dqa", "smoke", "synthesis", "tapeout"];
  if (stage === "dqa") return ["smoke", "verify", "synthesis", "tapeout"];
  if (stage === "smoke") return ["verify", "synthesis", "tapeout"];
  if (stage === "verify") return ["smoke", "synthesis", "tapeout"];
  if (stage === "synthesis") return ["tapeout", "smoke", "verify"];
  return ["smoke", "verify"];
}

function stageKey(stage: ChainStage): string {
  if (stage === "synthesis") return "arch2synthesis";
  if (stage === "tapeout") return "arch2tapeout";
  return stage;
}

async function postJSON<T>(path: string, body: unknown): Promise<T> {
  const supabase = createClientComponentClient();
  const { data: { session } } = await supabase.auth.getSession();
  const headers: Record<string, string> = { "Content-Type": "application/json" };
  if (session?.user?.id) headers["x-user-id"] = session.user.id;
  if (session?.access_token) headers.Authorization = `Bearer ${session.access_token}`;

  const resp = await fetch(`${API_BASE}${path}`, {
    method: "POST",
    headers,
    body: JSON.stringify(body),
  });
  const text = await resp.text().catch(() => "");
  if (!resp.ok) {
    throw new Error(`${resp.status} ${resp.statusText}${text ? ` - ${text}` : ""}`);
  }
  return (text ? JSON.parse(text) : {}) as T;
}

export default function NextWorkflowLauncher({
  currentStage,
  currentWorkflowId,
  currentRunId,
  sourceArch2RTLWorkflowId,
  upstreamWorkflows,
  disabled = false,
  verifyTestIntent,
  verifyCoverageTargets,
  verifyQuerySuffix = "",
}: {
  currentStage: ChainStage;
  currentWorkflowId: string | null;
  currentRunId?: string | null;
  sourceArch2RTLWorkflowId: string | null;
  upstreamWorkflows?: Record<string, string | undefined | null>;
  disabled?: boolean;
  verifyTestIntent?: string;
  verifyCoverageTargets?: string;
  verifyQuerySuffix?: string;
}) {
  const router = useRouter();
  const options = useMemo(() => optionsForStage(currentStage), [currentStage]);
  const [action, setAction] = useState<NextAction>(options[0] || "verify");
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);
  const [started, setStarted] = useState<StartedRun | null>(null);
  const [startedStatus, setStartedStatus] = useState<string | null>(null);

  useEffect(() => {
    if (!started?.workflowId) return;
    const supabase = createClientComponentClient();
    let active = true;
    async function fetchStatus() {
      const { data } = await supabase
        .from("workflows")
        .select("status")
        .eq("id", started.workflowId)
        .maybeSingle();
      if (active && data?.status) setStartedStatus(String(data.status));
    }
    void fetchStatus();
    const timer = window.setInterval(fetchStatus, 2000);
    return () => {
      active = false;
      window.clearInterval(timer);
    };
  }, [started?.workflowId]);

  if (!currentWorkflowId || !sourceArch2RTLWorkflowId) return null;

  const mergedUpstream: Record<string, string> = {
    ...(upstreamWorkflows || {}),
    arch2rtl: sourceArch2RTLWorkflowId,
    [stageKey(currentStage)]: currentWorkflowId,
  };

  async function runNext() {
    if (!currentWorkflowId || !sourceArch2RTLWorkflowId) return;
    setErr(null);

    if (action === "verify") {
      const raw = window.localStorage.getItem(DESIGN_CHAIN_CONTEXT_KEY);
      let context: DesignChainContext = {};
      try {
        context = raw ? JSON.parse(raw) as DesignChainContext : {};
      } catch {
        context = {};
      }
      context.arch2rtlWorkflowId = sourceArch2RTLWorkflowId;
      context.arch2rtlRunId = currentStage === "arch2rtl" ? currentRunId || undefined : context.arch2rtlRunId;
      window.localStorage.setItem(DESIGN_CHAIN_CONTEXT_KEY, JSON.stringify(context));
      window.localStorage.setItem(VERIFY_HANDOFF_PREFILL_KEY, JSON.stringify({
        fromWorkflowId: sourceArch2RTLWorkflowId,
        fromRunId: currentRunId,
        testIntent: verifyTestIntent || GENERIC_VERIFY_INTENT,
        randomVsDirected: "directed",
        coverageTargets: verifyCoverageTargets || "Derived interface behavior, reset behavior, functional corner cases",
        simulatorType: "verilator",
        seedCount: 4,
        parentWorkflowId: currentWorkflowId,
        upstreamWorkflows: mergedUpstream,
      }));
      router.push(`/apps/verify?handoff=1${verifyQuerySuffix}`);
      return;
    }

    const payload = {
      rtl_source_mode: "from_arch2rtl",
      from_workflow_id: sourceArch2RTLWorkflowId,
      source_arch2rtl_workflow_id: sourceArch2RTLWorkflowId,
      parent_workflow_id: currentWorkflowId,
      upstream_workflows: mergedUpstream,
      start_stage: "synth",
      target: "asic",
      simulator_type: "verilator",
      seed_count: 4,
    };

    setRunning(true);
    try {
      const out = await postJSON<{ workflow_id: string; run_id?: string | null }>(ACTION_ENDPOINTS[action], payload);
      setStarted({ action, workflowId: out.workflow_id, runId: out.run_id });
      setStartedStatus("running");
    } catch (e) {
      setErr(e instanceof Error ? e.message : String(e));
    } finally {
      setRunning(false);
    }
  }

  return (
    <div className="rounded-xl border border-slate-800 bg-slate-950/70 p-3 text-sm">
      <label className="text-xs font-semibold uppercase tracking-wide text-cyan-200">Run next workflow</label>
      <div className="mt-2 grid gap-2 sm:grid-cols-[1fr_auto]">
        <select
          value={action}
          onChange={(event) => setAction(event.target.value as NextAction)}
          className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-slate-100 outline-none focus:border-cyan-400"
        >
          {options.map((option) => (
            <option key={option} value={option}>{ACTION_LABELS[option]}</option>
          ))}
        </select>
        <button
          onClick={runNext}
          disabled={disabled || running}
          className="rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
        >
          {action === "verify" ? "Open" : running ? "Starting..." : "Run"}
        </button>
      </div>
      <div className="mt-2 text-xs text-slate-400">
        Source RTL: <span className="break-all text-slate-200">{sourceArch2RTLWorkflowId}</span>
      </div>
      {err ? <div className="mt-2 rounded-lg border border-red-900 bg-red-950/40 p-2 text-xs text-red-200">{err}</div> : null}
      {started ? (
        <div className="mt-3 rounded-lg border border-cyan-900/70 bg-cyan-950/30 p-2 text-xs text-cyan-100">
          Started {ACTION_LABELS[started.action]}: <span className="break-all">{started.workflowId}</span>
          {started.runId ? <span className="block break-all text-cyan-200">run: {started.runId}</span> : null}
          <span className="mt-1 block text-cyan-200">status: {startedStatus || "queued"}</span>
          <div className="mt-2 flex flex-wrap gap-2">
            <button
              onClick={() => window.open(`${API_BASE}/workflow/${started.workflowId}/download_zip?full=1`, "_blank")}
              className="rounded-md bg-slate-800 px-3 py-1.5 text-slate-100 hover:bg-slate-700"
            >
              Download ZIP
            </button>
          </div>
          <div className="mt-3">
            <NextWorkflowLauncher
              currentStage={started.action === "synthesis" ? "synthesis" : started.action === "tapeout" ? "tapeout" : started.action}
              currentWorkflowId={started.workflowId}
              currentRunId={started.runId}
              sourceArch2RTLWorkflowId={sourceArch2RTLWorkflowId}
              upstreamWorkflows={{ ...mergedUpstream, [stageKey(started.action === "synthesis" ? "synthesis" : started.action === "tapeout" ? "tapeout" : started.action)]: started.workflowId }}
              disabled={startedStatus !== "completed"}
            />
          </div>
        </div>
      ) : null}
    </div>
  );
}
