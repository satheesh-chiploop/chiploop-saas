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

function firstNumber(...values: unknown[]): number {
  for (const value of values) {
    if (typeof value === "number" && Number.isFinite(value)) return value;
  }
  return 0;
}

function firstString(...values: unknown[]): string {
  for (const value of values) {
    if (typeof value === "string" && value.trim()) return value.trim();
  }
  return "";
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
      embedded: ["system_firmware_dashboard.json", "system_firmware_execution.json"],
      software: ["system_software_api_contract.json", "system_software_package.json"],
      validation: [
        "system_software_validation_summary_l2.json",
        "system_cosim_trace_validation_report.json",
        "system_cosim_execution_report.json",
        "system_cosim_harness_manifest.json",
        "system_software_validation_summary.json",
        "build_validation_report.json",
        "test_execution_report.json",
        "mock_runtime_validation_report.json",
        "package_audit_report.json",
        "contract_consistency_report.json",
      ],
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
      const execution = evidence["system_firmware_execution.json"] || {};
      const readiness = record(execution.readiness);
      const inputs = record(execution.inputs);
      const missingInputs = array(dashboard.missing_inputs).length
        ? array(dashboard.missing_inputs).map(String)
        : array(readiness.missing).map(String);
      const firmwareElfPlaceholder = dashboard.firmware_elf_placeholder === true || inputs.firmware_elf_placeholder === true;
      const passed = number(dashboard.passed_test_count);
      const failed = number(dashboard.failed_test_count);
      const executed = number(dashboard.executed_test_count);
      return (
        <div className="mt-5 space-y-5">
          {missingInputs.length ? (
            <div className="rounded-lg border border-amber-700/60 bg-amber-950/20 p-4">
              <div className="text-sm font-semibold text-amber-200">Blocked inputs</div>
              <div className="mt-2 text-sm text-amber-100">{missingInputs.join(", ")}</div>
              {firmwareElfPlaceholder ? (
                <div className="mt-2 text-xs text-slate-300">
                  Firmware generation produced a placeholder ELF. Check the ELF build debug artifact and ensure Cargo is installed in the backend runtime.
                </div>
              ) : null}
            </div>
          ) : null}
          <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
            <div className="space-y-3">
              <Bar label="Co-simulation passed" value={passed} total={executed} color="bg-emerald-500" />
              <Bar label="Co-simulation failed" value={failed} total={executed} color="bg-rose-500" />
            </div>
            <div className="grid grid-cols-2 gap-3">
              <Stat title="Status" value={String(dashboard.overall_status || "unavailable")} />
              <Stat title="Executed" value={executed} />
              <Stat title="ELF" value={firmwareElfPlaceholder ? "placeholder" : String(dashboard.firmware_elf_detected ? "detected" : "missing")} />
              <Stat title="Missing Inputs" value={missingInputs.length} />
            </div>
          </div>
        </div>
      );
    }

    if (stage === "software") {
      const api = evidence["system_software_api_contract.json"] || {};
      const pkg = evidence["system_software_package.json"] || {};
      const groups = array(api.public_api_groups);
      const methods = groups.reduce<number>((sum, group) => sum + array(record(group).methods).length, 0);
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
    const execution = evidence["system_cosim_execution_report.json"] || {};
    const harness = evidence["system_cosim_harness_manifest.json"] || {};
    const softwareOnlySummary = evidence["system_software_validation_summary.json"] || {};
    const buildReport = evidence["build_validation_report.json"] || {};
    const testReport = evidence["test_execution_report.json"] || {};
    const mockReport = evidence["mock_runtime_validation_report.json"] || {};
    const packageReport = evidence["package_audit_report.json"] || {};
    const contractReport = evidence["contract_consistency_report.json"] || {};
    const validationArtifactsLoaded = Boolean(
      evidence["system_software_validation_summary_l2.json"] ||
      evidence["system_cosim_trace_validation_report.json"] ||
      evidence["system_cosim_execution_report.json"] ||
      evidence["system_cosim_harness_manifest.json"] ||
      evidence["system_software_validation_summary.json"] ||
      evidence["build_validation_report.json"] ||
      evidence["test_execution_report.json"] ||
      evidence["mock_runtime_validation_report.json"] ||
      evidence["package_audit_report.json"] ||
      evidence["contract_consistency_report.json"]
    );
    if (!validationArtifactsLoaded) {
      return (
        <div className="mt-5 rounded-lg border border-amber-700/60 bg-amber-950/20 p-4 text-sm text-amber-100">
          Validation artifacts are still syncing or were not found for this workflow yet. Use Download ZIP to confirm the generated artifact names.
        </div>
      );
    }

    if (softwareOnlySummary.validation_scope === "software_only" || evidence["system_software_validation_summary.json"]) {
      const checks = [
        { label: "Build", status: firstString(softwareOnlySummary.build_status, buildReport.build_status, "unavailable") },
        { label: "Tests", status: firstString(softwareOnlySummary.test_status, testReport.test_status, "unavailable") },
        { label: "Contract", status: firstString(softwareOnlySummary.contract_status, contractReport.status, "unavailable") },
        { label: "Mock Runtime", status: firstString(softwareOnlySummary.mock_runtime_status, mockReport.mock_runtime_status, "unavailable") },
        { label: "Package", status: firstString(softwareOnlySummary.package_status, packageReport.package_status, "unavailable") },
      ];
      const passCount = checks.filter((item) => ["pass", "complete", "ready", "ok"].includes(item.status)).length;
      const failCount = checks.filter((item) => ["fail", "failed", "not_ready", "blocked", "error"].includes(item.status)).length;
      const totalChecks = checks.length;
      const blockingIssues = array(softwareOnlySummary.blocking_issues).map(String);
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
            <div className="space-y-3">
              <Bar label="Checks passed" value={passCount} total={totalChecks} color="bg-emerald-500" />
              <Bar label="Checks failed" value={failCount} total={totalChecks} color="bg-rose-500" />
            </div>
            <div className="grid grid-cols-2 gap-3">
              <Stat title="Verdict" value={String(softwareOnlySummary.overall_status || "unavailable")} />
              <Stat title="Checks" value={totalChecks} />
              <Stat title="Blocking Issues" value={blockingIssues.length} />
            </div>
          </div>
          <div className="overflow-hidden rounded-lg border border-slate-800">
            {checks.map((check) => (
              <div key={check.label} className="flex items-center justify-between border-b border-slate-800 px-4 py-3 text-sm last:border-b-0">
                <span className="text-slate-300">{check.label}</span>
                <span className="font-semibold text-slate-100">{check.status}</span>
              </div>
            ))}
          </div>
          {blockingIssues.length ? (
            <div className="rounded-lg border border-amber-700/60 bg-amber-950/20 p-4 text-sm text-amber-100">
              Blocking issues: {blockingIssues.join(", ")}
            </div>
          ) : null}
        </div>
      );
    }

    const traceScenarios = array(trace.scenario_validations);
    const executionScenarios = array(execution.scenario_results);
    const scenarios = traceScenarios.length ? traceScenarios : executionScenarios;
    const passed = firstNumber(summary.scenario_pass_count, trace.scenario_pass_count, execution.scenario_pass_count);
    const failed = firstNumber(summary.scenario_fail_count, trace.scenario_fail_count, execution.scenario_fail_count);
    const blocked = firstNumber(summary.scenario_blocked_count, execution.scenario_blocked_count);
    const notApplicable = firstNumber(summary.scenario_not_applicable_count, trace.scenario_not_applicable_count);
    const total = firstNumber(summary.scenario_count, trace.scenario_count, execution.scenario_count, scenarios.length);
    const verdict = firstString(
      summary.final_system_correctness_verdict,
      trace.trace_validation_status,
      execution.execution_status,
      harness.harness_status,
      "unavailable"
    );
    return (
      <div className="mt-5 space-y-5">
        <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
          <div className="space-y-3">
            <Bar label="Scenario passed" value={passed} total={total} color="bg-emerald-500" />
            <Bar label="Scenario failed" value={failed} total={total} color="bg-rose-500" />
            <Bar label="Scenario blocked" value={blocked} total={total} color="bg-amber-500" />
            <Bar label="Not applicable" value={notApplicable} total={total} color="bg-slate-500" />
          </div>
          <div className="grid grid-cols-2 gap-3">
            <Stat title="Verdict" value={verdict} />
            <Stat title="Scenarios" value={total} />
            <Stat title="Not Applicable" value={notApplicable} />
          </div>
        </div>
        {scenarios.length ? (
          <div className="overflow-hidden rounded-lg border border-slate-800">
            {scenarios.slice(0, 6).map((entry, index) => {
              const scenario = record(entry);
              const scenarioStatus = firstString(
                scenario.trace_validation_status,
                scenario.execution_status,
                scenario.status,
                "unavailable"
              );
              return (
                <div key={index} className="flex items-center justify-between border-b border-slate-800 px-4 py-3 text-sm last:border-b-0">
                  <span className="text-slate-300">{String(scenario.scenario_id || `scenario_${index + 1}`)}</span>
                  <span className="font-semibold text-slate-100">{scenarioStatus}</span>
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
