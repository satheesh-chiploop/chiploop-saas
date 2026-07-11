"use client";

import { useMemo } from "react";
import { useRouter } from "next/navigation";

export type HemChildRun = {
  label: string;
  workflowId: string;
  dashboardPath: string;
  status?: string;
};

export function parseHemChildRuns(logs: string | null | undefined): HemChildRun[] {
  if (!logs) return [];
  const runs: HemChildRun[] = [];
  const byWorkflowId = new Map<string, HemChildRun>();
  const byLabel = new Map<string, HemChildRun>();

  const startedPattern = /HEM started (.+?) workflow ([0-9a-f-]{36})(?:\. Dashboard: (\/dashboard\/[^\s]+))?/gi;
  for (const started of logs.matchAll(startedPattern)) {
    const label = started[1].trim();
    const workflowId = started[2];
    const dashboardPath = started[3] || `/dashboard/${workflowId}?stage=${label.toLowerCase()}&app=HEM`;
    if (byWorkflowId.has(workflowId)) continue;
    const item = {
      label,
      workflowId,
      dashboardPath,
      status: "running",
    };
    byWorkflowId.set(workflowId, item);
    byLabel.set(label.toLowerCase(), item);
    runs.push(item);
  }

  const finishedPattern = /HEM (.+?) finished with status (\w+)/gi;
  for (const finished of logs.matchAll(finishedPattern)) {
    const item = byLabel.get(finished[1].trim().toLowerCase());
    if (item) item.status = finished[2];
  }

  if (!runs.length) {
    const fallbackPattern = /\/dashboard\/([0-9a-f-]{36})\?stage=([^&\s]+)&app=HEM/gi;
    for (const match of logs.matchAll(fallbackPattern)) {
      const workflowId = match[1];
      if (byWorkflowId.has(workflowId)) continue;
      const stage = match[2];
      const label = stage === "verification" ? "Verification" : stage.charAt(0).toUpperCase() + stage.slice(1);
      const item = {
        label,
        workflowId,
        dashboardPath: match[0],
        status: "running",
      };
      byWorkflowId.set(workflowId, item);
      runs.push(item);
    }
  }

  return runs;
}

type HemControlsProps = {
  enabled: boolean;
  adaptive: boolean;
  onEnabledChange: (value: boolean) => void;
  onAdaptiveChange: (value: boolean) => void;
  currentStageLabel: string;
  nextStageLabel?: string | null;
  disabled?: boolean;
  disabledReason?: string;
};

export function HemAutomaticRunControls({
  enabled,
  adaptive,
  onEnabledChange,
  onAdaptiveChange,
  currentStageLabel,
  nextStageLabel,
  disabled = false,
  disabledReason,
}: HemControlsProps) {
  return (
    <div className="rounded-xl border border-cyan-900/50 bg-cyan-950/15 p-4 text-sm text-slate-300">
      <div className="text-xs leading-5 text-slate-400">
        <span className="font-semibold text-cyan-200">What is HEM?</span>{" "}
        Hebbian Engineering Memory helps ChipLoop continue to the next proven engineering step after a successful run.
        Fixed mode follows built-in policy. Adaptive mode also records outcomes for future learning.
      </div>
      {disabled ? (
        <div className="mt-3 rounded-lg border border-amber-900/50 bg-amber-950/20 p-3 text-xs text-amber-100">
          {disabledReason || "HEM needs a valid upstream workflow source for this stage."}
        </div>
      ) : null}
      <label className="mt-3 flex items-start gap-3">
        <input
          className="mt-1"
          type="checkbox"
          checked={enabled}
          disabled={disabled}
          onChange={(event) => onEnabledChange(event.target.checked)}
        />
        <span>
          <span className="font-semibold text-slate-100">Enable HEM Automatic Runs</span>
          <span className="mt-1 block text-xs text-slate-500">
            Next if {currentStageLabel} passes: {nextStageLabel || "record completion"}.
          </span>
        </span>
      </label>

      {enabled ? (
        <label className="mt-3 flex items-start gap-3">
          <input
            className="mt-1"
            type="checkbox"
            checked={adaptive}
            onChange={(event) => onAdaptiveChange(event.target.checked)}
          />
          <span>
            <span className="font-semibold text-slate-100">Use Adaptive HEM</span>
            <span className="mt-1 block text-xs text-slate-500">
              Starts from the fixed policy and records this run for later policy learning.
            </span>
          </span>
        </label>
      ) : null}
    </div>
  );
}

export function HemChildDashboardLinks({ logs }: { logs: string | null | undefined }) {
  const router = useRouter();
  const childRuns = useMemo(() => parseHemChildRuns(logs), [logs]);

  if (!childRuns.length) return null;

  return (
    <div className="mt-3 rounded-xl border border-cyan-900/50 bg-cyan-950/15 p-3 text-sm text-slate-300">
      <div className="font-semibold text-cyan-100">HEM child dashboards</div>
      <div className="mt-2 space-y-2">
        {childRuns.map((child) => (
          <div
            key={`${child.label}-${child.workflowId}`}
            className="flex flex-wrap items-center justify-between gap-2 rounded-lg border border-slate-800 bg-black/20 p-2"
          >
            <div>
              <div className="font-semibold text-slate-100">
                {child.label} <span className="text-xs text-slate-500">({child.status || "queued"})</span>
              </div>
              <div className="break-all text-xs text-slate-500">{child.workflowId}</div>
            </div>
            <button
              type="button"
              onClick={() => router.push(child.dashboardPath)}
              className="rounded-lg bg-cyan-700 px-3 py-2 text-xs font-semibold text-white hover:bg-cyan-600"
            >
              Open Dashboard
            </button>
          </div>
        ))}
      </div>
    </div>
  );
}
