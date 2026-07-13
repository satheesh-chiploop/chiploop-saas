"use client";

import { useEffect, useMemo, useState } from "react";
import { createClientComponentClient } from "@/lib/platformClient";

export type HemChildRun = {
  label: string;
  workflowId: string;
  dashboardPath: string;
  status?: string;
};

export type SystemHemGoal = "product_demo" | "implementation";

export type SystemHemStageToggleMap = Record<string, boolean>;

export const SYSTEM_HEM_GOAL_OPTIONS = [
  {
    value: "product_demo",
    label: "Product Demo",
    helper: "Continue through DQA, simulation, firmware, software, co-simulation, and product demo.",
  },
  {
    value: "implementation",
    label: "Implementation",
    helper: "Continue through DQA, synthesis, and physical design/tapeout handoff.",
  },
];

export const SYSTEM_HEM_DEFAULT_STAGE_TOGGLES: SystemHemStageToggleMap = {
  system_dqa: true,
  system_sim: true,
  system_firmware: true,
  system_software: true,
  system_validation: true,
  system_product: true,
  system_synthesis: true,
  system_pd: true,
};

export function systemHemStageOptions(goal: SystemHemGoal, toggles: SystemHemStageToggleMap) {
  const productStages = [
    ["system_dqa", "System DQA"],
    ["system_sim", "System Sim"],
    ["system_firmware", "Firmware"],
    ["system_software", "Software"],
    ["system_validation", "Co-simulation / Validation"],
    ["system_product", "Product Demo"],
  ];
  const implementationStages = [
    ["system_dqa", "System DQA"],
    ["system_synthesis", "System Synthesis"],
    ["system_pd", "System PD"],
  ];
  return (goal === "implementation" ? implementationStages : productStages).map(([key, label]) => ({
    key,
    label,
    enabled: toggles[key] ?? true,
  }));
}

const HEM_STAGE_ORDER = ["dqa", "verification", "firmware", "software", "validation", "product", "synthesis", "tapeout"];

function labelFromStage(stage: string): string {
  if (stage === "dqa") return "DQA";
  if (stage === "verification" || stage === "verify") return "Verification";
  if (stage === "firmware") return "Firmware";
  if (stage === "software") return "Software";
  if (stage === "validation") return "Co-simulation / Validation";
  if (stage === "product") return "Product Demo";
  if (stage === "synthesis" || stage === "arch2synthesis") return "Synthesis";
  if (stage === "tapeout" || stage === "arch2tapeout") return "Tapeout";
  return stage.charAt(0).toUpperCase() + stage.slice(1);
}

function stageFromLabel(label: string): string {
  const normalized = label.trim().toLowerCase();
  if (normalized === "dqa" || normalized === "system dqa") return "dqa";
  if (normalized === "verification" || normalized === "verify" || normalized === "system sim") return "verification";
  if (normalized === "firmware" || normalized === "system firmware") return "firmware";
  if (normalized === "software" || normalized === "system software") return "software";
  if (normalized === "validation" || normalized === "co-simulation / validation" || normalized === "co-simulation" || normalized === "system validation") return "validation";
  if (normalized === "product demo" || normalized === "product app") return "product";
  if (normalized === "synthesis" || normalized === "arch2synthesis" || normalized === "system synthesis") return "synthesis";
  if (normalized === "tapeout" || normalized === "arch2tapeout" || normalized === "system pd") return "tapeout";
  return normalized.replace(/\s+/g, "-");
}

export function parseHemChildRuns(logs: string | null | undefined): HemChildRun[] {
  if (!logs) return [];
  const runs: HemChildRun[] = [];
  const byWorkflowId = new Map<string, HemChildRun>();
  const byLabel = new Map<string, HemChildRun>();
  const byStage = new Map<string, HemChildRun>();

  const startedPattern = /HEM started (.+?) workflow ([0-9a-f-]{36})(?:\. Dashboard: (\/dashboard\/[^\s]+))?/gi;
  for (const started of logs.matchAll(startedPattern)) {
    const label = started[1].trim();
    const workflowId = started[2];
    const dashboardPath = started[3] || `/dashboard/${workflowId}?stage=${stageFromLabel(label)}&app=HEM`;
    if (byWorkflowId.has(workflowId)) continue;
    const item = {
      label,
      workflowId,
      dashboardPath,
      status: "running",
    };
    byWorkflowId.set(workflowId, item);
    byLabel.set(label.toLowerCase(), item);
    byStage.set(stageFromLabel(label), item);
    runs.push(item);
  }

  const finishedPattern = /HEM (.+?) finished with status (\w+)/gi;
  for (const finished of logs.matchAll(finishedPattern)) {
    const label = finished[1].trim();
    const item = byLabel.get(label.toLowerCase()) || byStage.get(stageFromLabel(label));
    if (item) item.status = finished[2];
  }

  const completionPattern = /HEM Automatic Run \(.+?\) completed with respect to .+?: (.+?) completed\./gi;
  for (const completed of logs.matchAll(completionPattern)) {
    const completedLabels = completed[1]
      .split(",")
      .map((item) => item.trim())
      .filter(Boolean);
    for (const label of completedLabels) {
      const item = byLabel.get(label.toLowerCase()) || byStage.get(stageFromLabel(label));
      if (item) item.status = "completed";
    }
  }

  const fallbackPattern = /\/dashboard\/([0-9a-f-]{36})\?stage=([^&\s]+)&app=HEM/gi;
  for (const match of logs.matchAll(fallbackPattern)) {
    const workflowId = match[1];
    if (byWorkflowId.has(workflowId)) continue;
    const stage = match[2];
    const label = labelFromStage(stage);
    const item = {
      label,
      workflowId,
      dashboardPath: match[0],
      status: "running",
    };
    byWorkflowId.set(workflowId, item);
    byLabel.set(label.toLowerCase(), item);
    byStage.set(stageFromLabel(label), item);
    runs.push(item);
  }

  return runs.sort((a, b) => {
    const aIndex = HEM_STAGE_ORDER.indexOf(stageFromLabel(a.label));
    const bIndex = HEM_STAGE_ORDER.indexOf(stageFromLabel(b.label));
    return (aIndex === -1 ? 99 : aIndex) - (bIndex === -1 ? 99 : bIndex);
  });
}

type HemControlsProps = {
  enabled: boolean;
  adaptive: boolean;
  onEnabledChange: (value: boolean) => void;
  onAdaptiveChange: (value: boolean) => void;
  currentStageLabel: string;
  nextStageLabel?: string | null;
  goal?: string;
  onGoalChange?: (value: string) => void;
  goalOptions?: Array<{ value: string; label: string; helper?: string }>;
  stageOptions?: Array<{ key: string; label: string; enabled: boolean }>;
  onStageToggle?: (key: string, value: boolean) => void;
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
  goal,
  onGoalChange,
  goalOptions,
  stageOptions,
  onStageToggle,
  disabled = false,
  disabledReason,
}: HemControlsProps) {
  const selectedGoal = goalOptions?.find((option) => option.value === goal);

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
        <div className="mt-3 space-y-3">
          {Boolean(goalOptions?.length) && goal && onGoalChange ? (
            <div className="rounded-lg border border-slate-800 bg-black/20 p-3">
              <label className="text-xs font-semibold uppercase text-slate-400">HEM Goal</label>
              <select
                value={goal}
                onChange={(event) => onGoalChange(event.target.value)}
                className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm font-semibold text-slate-100"
              >
                {goalOptions.map((option) => (
                  <option key={option.value} value={option.value}>
                    {option.label}
                  </option>
                ))}
              </select>
              {selectedGoal?.helper ? <p className="mt-2 text-xs leading-5 text-slate-500">{selectedGoal.helper}</p> : null}
            </div>
          ) : null}

          {Boolean(stageOptions?.length) && onStageToggle ? (
            <div className="rounded-lg border border-slate-800 bg-black/20 p-3">
              <div className="text-xs font-semibold uppercase text-slate-400">Allowed automatic stages</div>
              <div className="mt-2 grid gap-2 sm:grid-cols-2">
                {stageOptions.map((stage) => (
                  <label key={stage.key} className="flex items-center gap-2 rounded-lg border border-slate-800 bg-slate-950/70 px-3 py-2 text-xs text-slate-300">
                    <input
                      type="checkbox"
                      checked={stage.enabled}
                      onChange={(event) => onStageToggle(stage.key, event.target.checked)}
                    />
                    <span>{stage.label}</span>
                  </label>
                ))}
              </div>
            </div>
          ) : null}

          <label className="flex items-start gap-3">
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
        </div>
      ) : null}
    </div>
  );
}

export function HemChildDashboardLinks({ logs }: { logs: string | null | undefined }) {
  const childRuns = useMemo(() => parseHemChildRuns(logs), [logs]);
  const workflowIds = useMemo(() => childRuns.map((child) => child.workflowId), [childRuns]);
  const workflowIdKey = workflowIds.join(",");
  const [workflowStatuses, setWorkflowStatuses] = useState<Record<string, string>>({});
  const supabase = useMemo(() => createClientComponentClient(), []);

  useEffect(() => {
    const ids = workflowIdKey.split(",").filter(Boolean);
    if (!ids.length) {
      setWorkflowStatuses({});
      return;
    }

    let active = true;
    let interval: ReturnType<typeof window.setInterval> | null = null;
    const fetchStatuses = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status")
        .in("id", ids);
      if (!active || error || !data) return;
      const nextStatuses: Record<string, string> = {};
      for (const row of data as Array<{ id: string; status?: string | null }>) {
        if (row.id && row.status) nextStatuses[row.id] = row.status;
      }
      setWorkflowStatuses(nextStatuses);
      const currentStatuses = ids.map((id) => nextStatuses[id]).filter(Boolean);
      const allTerminal =
        currentStatuses.length === ids.length &&
        currentStatuses.every((status) => ["completed", "failed", "cancelled", "stopped"].includes(status.toLowerCase()));
      if (allTerminal && interval) window.clearInterval(interval);
    };

    void fetchStatuses();
    interval = window.setInterval(() => {
      void fetchStatuses();
    }, 2500);

    return () => {
      active = false;
      if (interval) window.clearInterval(interval);
    };
  }, [supabase, workflowIdKey]);

  if (!childRuns.length) return null;

  return (
    <div className="mt-3 rounded-xl border border-cyan-900/50 bg-cyan-950/15 p-4 text-sm text-slate-300">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <div>
          <div className="font-semibold text-cyan-100">HEM Run Summary</div>
          <div className="mt-1 text-xs text-slate-500">
            Open each workflow dashboard to review generated artifacts, logs, and results.
          </div>
        </div>
        <div className="rounded-full border border-cyan-800/60 bg-black/20 px-3 py-1 text-xs text-cyan-100">
          {childRuns.length} linked workflow{childRuns.length === 1 ? "" : "s"}
        </div>
      </div>
      <div className="mt-3 overflow-x-auto rounded-xl border border-slate-800">
        <table className="w-full min-w-[720px] text-left text-xs">
          <thead className="bg-black/30 text-slate-400">
            <tr>
              <th className="px-3 py-2 font-semibold">Workflow</th>
              <th className="px-3 py-2 font-semibold">Status</th>
              <th className="px-3 py-2 font-semibold">Workflow ID</th>
              <th className="px-3 py-2 text-right font-semibold">Dashboard</th>
            </tr>
          </thead>
          <tbody>
            {childRuns.map((child) => (
              <tr key={`${child.label}-${child.workflowId}`} className="border-t border-slate-800 bg-black/10">
                <td className="px-3 py-3 font-semibold text-slate-100">{child.label}</td>
                <td className="px-3 py-3">
                  <span className="rounded-full border border-slate-700 bg-black/30 px-2 py-1 text-slate-300">
                    {workflowStatuses[child.workflowId] || child.status || "running"}
                  </span>
                </td>
                <td className="max-w-[340px] break-all px-3 py-3 font-mono text-[11px] text-slate-400">
                  {child.workflowId}
                </td>
                <td className="px-3 py-3 text-right">
                  <a
                    href={child.dashboardPath}
                    target="_blank"
                    rel="noreferrer"
                    className="rounded-lg bg-cyan-700 px-3 py-2 text-xs font-semibold text-white hover:bg-cyan-600"
                  >
                    Open Dashboard
                  </a>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}
