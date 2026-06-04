"use client";

import { useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import {
  DESIGN_CHAIN_CONTEXT_KEY,
  GENERIC_VERIFY_INTENT,
  VERIFY_HANDOFF_PREFILL_KEY,
  type DesignChainContext,
} from "@/lib/pwmFullStackDemo";

type ChainStage = "arch2rtl" | "dqa" | "smoke" | "synthesis" | "tapeout" | "verify";
type NextAction = "verify" | "dqa" | "smoke" | "synthesis" | "tapeout";

const ACTION_LABELS: Record<NextAction, string> = {
  verify: "Verification",
  dqa: "DQA checks",
  smoke: "Smoke simulation",
  synthesis: "Synthesis",
  tapeout: "Tapeout prep",
};

const ACTION_ROUTES: Record<NextAction, string> = {
  verify: "/apps/verify",
  dqa: "/apps/dqa",
  smoke: "/apps/smoke",
  synthesis: "/apps/arch2synthesis",
  tapeout: "/apps/arch2tapeout",
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

  if (!currentWorkflowId || !sourceArch2RTLWorkflowId) return null;

  const mergedUpstream: Record<string, string> = Object.fromEntries(
    Object.entries({
      ...(upstreamWorkflows || {}),
      arch2rtl: sourceArch2RTLWorkflowId,
      [stageKey(currentStage)]: currentWorkflowId,
    }).filter((entry): entry is [string, string] => typeof entry[1] === "string" && Boolean(entry[1]))
  );

  async function runNext() {
    if (!currentWorkflowId || !sourceArch2RTLWorkflowId) return;

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

    const params = new URLSearchParams({
      handoff: "1",
      from_workflow_id: sourceArch2RTLWorkflowId,
      source_arch2rtl_workflow_id: sourceArch2RTLWorkflowId,
      parent_workflow_id: currentWorkflowId,
      upstream_workflows: JSON.stringify(mergedUpstream),
    });
    router.push(`${ACTION_ROUTES[action]}?${params.toString()}`);
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
          disabled={disabled}
          className="rounded-lg bg-cyan-600 px-4 py-2 font-semibold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
        >
          Open
        </button>
      </div>
      <div className="mt-2 text-xs text-slate-400">
        Source RTL: <span className="break-all text-slate-200">{sourceArch2RTLWorkflowId}</span>
      </div>
    </div>
  );
}
