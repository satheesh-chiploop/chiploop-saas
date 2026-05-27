"use client";

import { useEffect, useMemo, useState } from "react";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type Stage = "arch2rtl" | "verification" | "embedded" | "software" | "validation";
type JsonMap = Record<string, unknown>;

type Props = {
  workflowId: string | null;
  status?: string | null;
  stage: Stage;
};

const FLOW: Array<{ id: Stage; label: string }> = [
  { id: "arch2rtl", label: "RTL" },
  { id: "verification", label: "Verify" },
  { id: "embedded", label: "Firmware" },
  { id: "software", label: "Software" },
  { id: "validation", label: "Validation" },
];

function record(value: unknown): JsonMap {
  return value && typeof value === "object" && !Array.isArray(value) ? value as JsonMap : {};
}

function array(value: unknown): unknown[] {
  return Array.isArray(value) ? value : [];
}

function number(value: unknown): number {
  return typeof value === "number" && Number.isFinite(value) ? value : 0;
}

async function artifact(workflowId: string, filename: string): Promise<JsonMap | null> {
  try {
    return record(
      await apiGet<JsonMap>(
        `/apps/dashboard/artifact/${workflowId}?filename=${encodeURIComponent(filename)}`
      )
    );
  } catch (reason) {
    if (reason instanceof ApiClientError && reason.status === 404) return null;
    throw reason;
  }
}

function Stat({ title, value }: { title: string; value: string | number }) {
  return (
    <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="text-xs text-slate-400">{title}</div>
      <div className="mt-1 text-base font-semibold text-slate-100">{value}</div>
    </div>
  );
}

function Bar({ label, value, total, color }: { label: string; value: number; total: number; color: string }) {
  const width = total > 0 ? Math.max((value / total) * 100, value > 0 ? 5 : 0) : 0;
  return (
    <div className="space-y-1">
      <div className="flex justify-between text-xs text-slate-300">
        <span>{label}</span>
        <span>{value}</span>
      </div>
      <div className="h-3 overflow-hidden rounded bg-slate-800">
        <div className={`h-full rounded ${color}`} style={{ width: `${width}%` }} />
      </div>
    </div>
  );
}

export default function WorkflowEvidenceDashboard({ workflowId, status, stage }: Props) {
  const [evidence, setEvidence] = useState<Record<string, JsonMap | null>>({});
  const [error, setError] = useState<string | null>(null);
  const stageIndex = FLOW.findIndex((item) => item.id === stage);

  useEffect(() => {
    if (!workflowId || status !== "completed") return;
    let active = true;
    const files: Record<Stage, string[]> = {
      arch2rtl: ["digital_regmap.json"],
      verification: ["simulation_summary_coverage.json"],
      embedded: ["system_firmware_dashboard.json"],
      software: ["system_software_api_contract.json", "system_software_package.json"],
      validation: ["system_software_validation_summary_l2.json", "system_cosim_trace_validation_report.json"],
    };
    Promise.all(files[stage].map(async (filename) => [filename, await artifact(workflowId, filename)] as const))
      .then((entries) => {
        if (active) setEvidence(Object.fromEntries(entries));
      })
      .catch((reason: unknown) => {
        if (active) setError(reason instanceof Error ? reason.message : String(reason));
      });
    return () => {
      active = false;
    };
  }, [workflowId, stage, status]);

  const content = useMemo(() => {
    if (!workflowId || status !== "completed") {
      return <div className="mt-5 text-sm text-slate-400">Results appear after this stage completes.</div>;
    }
    if (error) return <div className="mt-5 text-sm text-amber-300">{error}</div>;

    if (stage === "arch2rtl") {
      const registers = array(record(evidence["digital_regmap.json"]?.regmap).registers);
      return registers.length ? (
        <div className="mt-5">
          <div className="text-sm font-semibold text-slate-100">Generated Firmware Register Interface</div>
          <div className="mt-3 grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {registers.slice(0, 8).map((item, index) => {
              const register = record(item);
              return (
                <div key={`${String(register.name || "register")}-${index}`} className="rounded-lg border border-cyan-900/60 bg-cyan-950/15 p-3">
                  <div className="text-xs text-cyan-300">{String(register.offset || "-")}</div>
                  <div className="mt-1 font-semibold text-slate-100">{String(register.name || "REGISTER")}</div>
                  <div className="mt-1 text-xs text-slate-400">{String(register.access || "")}</div>
                </div>
              );
            })}
          </div>
        </div>
      ) : <div className="mt-5 text-sm text-amber-300">Register-map artifact is not available for this completed run.</div>;
    }

    if (stage === "verification") {
      const simulation = record(evidence["simulation_summary_coverage.json"]?.simulation);
      const coverage = record(evidence["simulation_summary_coverage.json"]?.coverage);
      const passed = number(simulation.pass);
      const failed = number(simulation.fail);
      const total = number(simulation.total);
      const coveragePct = typeof coverage.functional_coverage_pct === "number" ? `${coverage.functional_coverage_pct}%` : "Unavailable";
      return (
        <div className="mt-5 grid gap-5 lg:grid-cols-[1fr_280px]">
          <div className="space-y-3">
            <Bar label="Simulation passed" value={passed} total={total} color="bg-emerald-500" />
            <Bar label="Simulation failed" value={failed} total={total} color="bg-rose-500" />
          </div>
          <div className="grid grid-cols-2 gap-3">
            <Stat title="Runs" value={total} />
            <Stat title="Functional Coverage" value={coveragePct} />
          </div>
        </div>
      );
    }

    if (stage === "embedded") {
      const dashboard = evidence["system_firmware_dashboard.json"] || {};
      const passed = number(dashboard.passed_test_count);
      const failed = number(dashboard.failed_test_count);
      const executed = number(dashboard.executed_test_count);
      return (
        <div className="mt-5 grid gap-5 lg:grid-cols-[1fr_320px]">
          <div className="space-y-3">
            <Bar label="Co-simulation passed" value={passed} total={executed} color="bg-emerald-500" />
            <Bar label="Co-simulation failed" value={failed} total={executed} color="bg-rose-500" />
          </div>
          <div className="grid grid-cols-2 gap-3">
            <Stat title="Status" value={String(dashboard.overall_status || "unavailable")} />
            <Stat title="Executed" value={executed} />
          </div>
        </div>
      );
    }

    if (stage === "software") {
      const api = evidence["system_software_api_contract.json"] || {};
      const pkg = evidence["system_software_package.json"] || {};
      const groups = array(api.public_api_groups);
      const methods = groups.reduce((sum, group) => sum + array(record(group).methods).length, 0);
      const artifacts = number(pkg.artifact_count);
      return (
        <div className="mt-5 grid gap-5 lg:grid-cols-[1fr_300px]">
          <div>
            <div className="text-sm font-semibold text-slate-100">Generated Software Interface</div>
            <div className="mt-3 flex flex-wrap gap-2">
              {groups.slice(0, 6).map((group, index) => (
                <span key={index} className="rounded border border-cyan-900/60 bg-cyan-950/20 px-3 py-2 text-xs text-cyan-200">
                  {String(record(group).name || "api_group")}
                </span>
              ))}
            </div>
          </div>
          <div className="grid grid-cols-2 gap-3">
            <Stat title="API Methods" value={methods} />
            <Stat title="Artifacts" value={artifacts} />
            <Stat title="Package" value={String(pkg.package_status || "unavailable")} />
          </div>
        </div>
      );
    }

    const summary = evidence["system_software_validation_summary_l2.json"] || {};
    const trace = evidence["system_cosim_trace_validation_report.json"] || {};
    const passed = number(summary.scenario_pass_count);
    const failed = number(summary.scenario_fail_count);
    const blocked = number(summary.scenario_blocked_count);
    const total = number(summary.scenario_count);
    const scenarios = array(trace.scenario_validations);
    return (
      <div className="mt-5 space-y-5">
        <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
          <div className="space-y-3">
            <Bar label="Scenario passed" value={passed} total={total} color="bg-emerald-500" />
            <Bar label="Scenario failed" value={failed} total={total} color="bg-rose-500" />
            <Bar label="Scenario blocked" value={blocked} total={total} color="bg-amber-500" />
          </div>
          <div className="grid grid-cols-2 gap-3">
            <Stat title="Verdict" value={String(summary.final_system_correctness_verdict || "unavailable")} />
            <Stat title="Scenarios" value={total} />
          </div>
        </div>
        {scenarios.length ? (
          <div className="overflow-hidden rounded-lg border border-slate-800">
            {scenarios.slice(0, 6).map((entry, index) => {
              const scenario = record(entry);
              return (
                <div key={index} className="flex items-center justify-between border-b border-slate-800 px-4 py-3 text-sm last:border-b-0">
                  <span className="text-slate-300">{String(scenario.scenario_id || `scenario_${index + 1}`)}</span>
                  <span className="font-semibold text-slate-100">{String(scenario.trace_validation_status || "unavailable")}</span>
                </div>
              );
            })}
          </div>
        ) : null}
      </div>
    );
  }, [evidence, error, stage, status, workflowId]);

  return (
    <section className="rounded-lg border border-slate-800 bg-slate-950/45 p-5">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div>
          <div className="text-sm font-semibold text-white">Demo Evidence Dashboard</div>
          <div className="mt-1 text-xs text-slate-400">Rendered from generated workflow artifacts.</div>
        </div>
        <div className="flex items-center gap-2">
          {FLOW.map((item, index) => (
            <div key={item.id} className="flex items-center gap-2">
              <div className={`rounded px-2 py-1 text-xs ${index <= stageIndex ? "bg-cyan-500/20 text-cyan-200" : "bg-slate-800 text-slate-500"}`}>
                {item.label}
              </div>
              {index < FLOW.length - 1 ? <span className="text-slate-600">&gt;</span> : null}
            </div>
          ))}
        </div>
      </div>
      {content}
    </section>
  );
}
