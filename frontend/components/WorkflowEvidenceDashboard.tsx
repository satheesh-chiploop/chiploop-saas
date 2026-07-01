"use client";

import { useEffect, useMemo, useState } from "react";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type Stage = "arch2rtl" | "dqa" | "smoke" | "synthesis" | "tapeout" | "verification" | "embedded" | "software" | "validation" | "product";
type JsonMap = Record<string, unknown>;

type Props = {
  workflowId: string | null;
  status?: string | null;
  stage: Stage;
  logs?: string | null;
};

type FlowItem = { id: Stage; label: string };

const RTL_STAGE: FlowItem = { id: "arch2rtl", label: "RTL" };

const MAIN_FLOW: FlowItem[] = [
  RTL_STAGE,
  { id: "verification", label: "Verify" },
  { id: "embedded", label: "Firmware" },
  { id: "software", label: "Software" },
  { id: "validation", label: "Validation" },
  { id: "product", label: "Product" },
];

const OPTIONAL_DIGITAL_FLOW: Record<Extract<Stage, "dqa" | "smoke" | "synthesis" | "tapeout">, FlowItem> = {
  dqa: { id: "dqa", label: "DQA" },
  smoke: { id: "smoke", label: "Smoke" },
  synthesis: { id: "synthesis", label: "Synth" },
  tapeout: { id: "tapeout", label: "Tapeout" },
};

function displayedFlow(stage: Stage): FlowItem[] {
  if (stage === "dqa" || stage === "smoke" || stage === "synthesis" || stage === "tapeout") {
    return [RTL_STAGE, OPTIONAL_DIGITAL_FLOW[stage]];
  }
  return MAIN_FLOW;
}

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

function firstPresent(...values: unknown[]): unknown {
  for (const value of values) {
    if (value !== undefined && value !== null && value !== "") return value;
  }
  return undefined;
}

function metricValue(...values: unknown[]): string | number {
  const value = firstPresent(...values);
  if (typeof value === "number" && Number.isFinite(value)) return formatNumber(value);
  if (typeof value === "string" && value.trim()) return value.trim();
  return "not produced";
}

function signedMetric(...values: unknown[]): string | number {
  const value = firstPresent(...values);
  if (typeof value === "number" && Number.isFinite(value)) return formatNumber(value);
  if (typeof value === "string" && value.trim()) return value.trim();
  return "not run";
}

function zeroWhenClean(status: unknown, value: unknown): unknown {
  if (value !== undefined && value !== null && value !== "") return value;
  const text = typeof status === "string" ? status.trim().toLowerCase() : "";
  return ["ok", "clean", "pass", "completed", "generated"].includes(text) ? 0 : value;
}

function formatNumber(value: number): string | number {
  if (!Number.isFinite(value)) return "not produced";
  if (Number.isInteger(value)) return value;
  return Number(value.toFixed(3)).toString();
}

function unprovenMetric(status: unknown, value: unknown): string | number {
  const text = typeof status === "string" ? status.trim().toLowerCase() : "";
  if (["pass", "ok", "clean"].includes(text)) return 0;
  return metricValue(value);
}

function pct(value: unknown): string {
  return typeof value === "number" && Number.isFinite(value) ? `${value}%` : "Unavailable";
}

function pctWithStatus(value: unknown, status: unknown): string {
  if (typeof value === "number" && Number.isFinite(value)) return `${value}%`;
  const text = typeof status === "string" && status.trim() ? status.trim() : "";
  if (text === "not_reported_by_verilator_lcov" || text === "not_reported_by_verilator_annotate_points") return "Not reported";
  return text ? `Unavailable (${text})` : "Unavailable";
}

function statusLabel(value: unknown): string {
  const text = typeof value === "string" && value.trim() ? value.trim() : "not_enabled";
  return text.replaceAll("_", " ");
}

function dftDashboardStatus(dft: JsonMap): string {
  const status = firstString(dft.status);
  if (status === "scan_cell_mapping_required") return "scan-cell mapping required";
  if (status === "scan_not_inserted") return "scan not inserted";
  return statusLabel(status);
}

function atpgDashboardStatus(atpg: JsonMap): string {
  const status = firstString(atpg.status);
  const reason = firstString(atpg.reason);
  if (reason === "scan_cell_mapping_required") return "blocked: scan-cell mapping required";
  if (status === "tool_detected_needs_adapter_command") return "adapter command required";
  if (status === "adapter_completed_no_metrics") return "adapter ran: no metrics";
  if (status === "adapter_completed_no_patterns") return "adapter ran: no patterns";
  if (status === "patterns_generated") return "patterns generated";
  if (status === "adapter_command_missing") return "adapter command missing";
  if (status === "adapter_failed") return "adapter failed";
  return statusLabel(status);
}

function atpgMetric(status: unknown, ...values: unknown[]): string | number {
  const text = typeof status === "string" ? status.trim() : "";
  if (text === "not_applicable") return "not applicable";
  if (text !== "patterns_generated") return "not produced";
  return metricValue(...values);
}

function scanMetric(status: unknown, value: unknown): string | number {
  const text = typeof status === "string" ? status.trim() : "";
  if (text === "not_applicable" || text === "scan_not_inserted" || text === "scan_cell_mapping_required" || text === "no_scan_flops" || text === "tool_unavailable") {
    return "not applicable";
  }
  return metricValue(value);
}

function lecDashboardStatus(lec: JsonMap): string {
  const status = firstString(lec.status);
  if (status === "missing_cell_library") return "setup issue: missing liberty";
  if (status === "missing_stdcell_models") return "setup issue: missing stdcell models";
  if (status === "incomplete_stdcell_models") return "setup issue: incomplete stdcell models";
  if (status === "inconclusive_unresolved_cells") return "inconclusive: unresolved cells";
  if (status === "inconclusive_missing_sat_models") return "inconclusive: missing SAT models";
  return statusLabel(status);
}

function findingCount(report: JsonMap): number {
  return array(report.findings).length
    + array(report.heuristic_issues).length
    + array(report.synthesizable_subset_findings).length
    + array(record(report.yosys).errors).length;
}

function uniqueStrings(values: unknown[]): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  for (const value of values) {
    const text = typeof value === "string" ? value.trim() : "";
    if (!text || seen.has(text)) continue;
    seen.add(text);
    out.push(text);
  }
  return out;
}

function boolToolNames(tools: JsonMap): string[] {
  return Object.entries(tools)
    .filter(([, value]) => value === true)
    .map(([key]) => key);
}

function dqaToolSummary(lint: JsonMap, readiness: JsonMap, executionSummary: JsonMap, profileSummary: JsonMap) {
  const lintTooling = record(lint.tooling);
  const lintProfile = record(lintTooling.tool_profile);
  const summaryProfile = record(executionSummary.tool_profile);
  const explicitProfile = Object.keys(profileSummary).length ? profileSummary : {};
  const executions = [
    ...array(lintTooling.executions),
    ...array(executionSummary.executions),
  ].map(record);
  const yosys = record(readiness.yosys);
  const used = uniqueStrings([
    ...executions.map((item) => item.tool),
    yosys.available === true ? "yosys" : "",
  ]);
  const detected = boolToolNames(record(readiness.tools_detected));
  const profileTools = [
    ...array(lintProfile.tools),
    ...array(summaryProfile.tools),
    ...array(explicitProfile.tools),
  ];
  const available = uniqueStrings([...used, ...detected, ...profileTools]);
  return {
    used,
    available,
    defaultTool: used.join(" / ") || "not reported",
  };
}

function lintVerdict(report: JsonMap): string {
  if (!Object.keys(report).length) return "unavailable";
  const verilator = record(report.verilator_lint);
  if (verilator.available === false) return "unavailable";
  const rc = verilator.returncode;
  const issues = array(report.heuristic_issues);
  if (typeof rc === "number" && rc !== 0) return `fail (rc ${rc})`;
  if (issues.some((issue) => String(record(issue).severity || "").toLowerCase() === "warning")) return "warning";
  return "pass";
}

function findingsVerdict(report: JsonMap): string {
  if (!Object.keys(report).length) return "unavailable";
  const findings = array(report.findings);
  if (!findings.length) return "pass";
  const hasError = findings.some((item) => {
    const severity = String(record(item).severity || "").toLowerCase();
    return severity === "error" || severity === "critical" || severity === "fail";
  });
  return hasError ? "fail" : "warning";
}

function synthesisReadinessVerdict(report: JsonMap): string {
  if (!Object.keys(report).length) return "unavailable";
  const score = number(report.score);
  const yosys = record(report.yosys);
  if (yosys.available === false) return "unavailable";
  const errors = array(yosys.errors).length;
  if (errors > 0) return "fail";
  if (score >= 80) return "pass";
  if (score >= 60) return "warning";
  return "fail";
}

function synthesisStatus(summary: JsonMap): string {
  const status = firstString(summary.status, summary.verdict);
  const rc = summary.return_code;
  if (status === "ok" || status === "pass" || status === "passed") return "pass";
  if (status === "failed" || status === "fail") return typeof rc === "number" ? `fail (rc ${rc})` : "fail";
  return status || "not produced";
}

function sdcStatus(setup: JsonMap, synthSummary: JsonMap): string {
  const setupStatus = firstString(setup.status);
  const outputs = record(setup.outputs);
  const inputs = record(synthSummary.inputs);
  const sdc = firstString(outputs.sdc, inputs.sdc, record(synthSummary.outputs).sdc);
  const synthStatus = firstString(synthSummary.status);
  if (setupStatus === "ok" && sdc) return "pass";
  if (synthStatus === "failed" && firstString(synthSummary.error).toLowerCase().includes("sdc")) return "fail";
  return sdc ? "available" : "not produced";
}

function timingViolationValue(wns: unknown, tns: unknown, explicit: unknown): string | number {
  const direct = firstPresent(explicit);
  if (typeof direct === "number" && Number.isFinite(direct)) return direct;
  const w = typeof wns === "number" && Number.isFinite(wns) ? wns : Number.NaN;
  const t = typeof tns === "number" && Number.isFinite(tns) ? tns : Number.NaN;
  if (Number.isFinite(w) || Number.isFinite(t)) return w < 0 || t < 0 ? "violated" : "0";
  return "not run";
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

function hasTerminalEvidence(status: string | null | undefined, stage: Stage, logs: string | null | undefined): boolean {
  const normalized = String(status || "").toLowerCase();
  if (["completed", "complete", "success", "succeeded", "failed", "done"].includes(normalized)) return true;
  if (!logs) return false;
  if (/(?:system|digital|embedded|analog|validation)\s+(?:run\s+)?app\s+complete/i.test(logs)) return true;
  if (/system\s+app\s+complete:\s*system[_\s-]*(?:firmware|software|software[_\s-]*validation|product[_\s-]*app[_\s-]*builder|rtl|sim)/i.test(logs)) {
    return true;
  }
  if (stage === "embedded") {
    return /system[_\s-]*firmware.*(?:cosim|coverage|dashboard|complete|generated)|system_software_handoff/i.test(logs);
  }
  if (stage === "software") {
    return /system\s+software\s+(?:packaging|executive\s+summary).*done|system_software_(?:package|executive_summary|api_contract)\.json/i.test(logs);
  }
  if (stage === "validation") {
    return /system\s+software\s+validation\s+summary.*done|(?:l2_)?validation_summary\.json|system_software_validation_summary(?:_l2)?\.json|system_cosim_trace_validation_report\.json/i.test(logs);
  }
  if (stage === "product") {
    return /system\s+product\s+(?:package|dashboard|capability|collateral).*done|system_product_(?:package|dashboard_manifest|capability_model|collateral_contract)\.json|system\/product\/app\/index\.html/i.test(logs);
  }
  return false;
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
    if (reason instanceof ApiClientError && reason.status >= 500) return null;
    throw reason;
  }
}

function stageEvidenceReady(stage: Stage, evidence: Record<string, JsonMap | null>): boolean {
  const has = (key: string) => Object.keys(record(evidence[key])).length > 0;
  if (stage === "product") {
    return has("system_product_dashboard_manifest.json") || has("system_product_package.json");
  }
  return Object.values(evidence).some((value) => Object.keys(record(value)).length > 0);
}

function Stat({ title, value }: { title: string; value: string | number }) {
  return (
    <div className="min-w-0 rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="text-xs text-slate-400">{title}</div>
      <div className="mt-1 min-h-6 break-words text-base font-semibold leading-snug text-slate-100">{value}</div>
    </div>
  );
}

function ToolStrip({ used, defaultTool }: { used: string[]; defaultTool: string }) {
  return (
    <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="min-w-0">
        <div className="text-xs text-slate-400">Tools Used</div>
        <div className="mt-1 break-words text-base font-semibold leading-snug text-slate-100">{defaultTool}</div>
        <div className="mt-2 flex gap-2 overflow-x-auto pb-1">
          {used.map((tool) => (
            <span key={tool} className="shrink-0 rounded border border-slate-700 bg-slate-950 px-2.5 py-1 text-xs font-semibold text-cyan-100">
              {tool}
            </span>
          ))}
          {!used.length ? <span className="text-sm text-slate-500">not reported</span> : null}
        </div>
      </div>
    </div>
  );
}

function CheckCard({ title, status, detail }: { title: string; status: string; tool?: string; detail?: string | number }) {
  return (
    <div className="min-w-0 rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="text-xs text-slate-400">{title}</div>
      <div className="mt-1 break-words text-base font-semibold leading-snug text-slate-100">{status}</div>
      {detail !== undefined ? <div className="mt-2 text-xs text-slate-500">{detail}</div> : null}
    </div>
  );
}

function CheckTable({ rows }: { rows: Array<{ check: string; status: string; detail: string; tool: string }> }) {
  return (
    <div className="overflow-x-auto rounded-lg border border-slate-800">
      <div className="min-w-[640px]">
        <div className="grid grid-cols-[1fr_1fr_1.4fr_1fr] border-b border-slate-800 bg-slate-950/70 px-4 py-2 text-xs font-semibold uppercase text-slate-400">
          <div>Check</div>
          <div>Status</div>
          <div>Evidence</div>
          <div>Tool</div>
        </div>
        {rows.map((row) => (
          <div key={row.check} className="grid grid-cols-[1fr_1fr_1.4fr_1fr] border-b border-slate-800 px-4 py-3 text-sm last:border-b-0">
            <div className="text-slate-300">{row.check}</div>
            <div className="font-semibold text-slate-100">{row.status}</div>
            <div className="text-slate-400">{row.detail}</div>
            <div className="text-cyan-100">{row.tool}</div>
          </div>
        ))}
      </div>
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

function MiniMetric({ label, value }: { label: string; value: string | number }) {
  return (
    <div className="min-w-0 rounded-md border border-slate-800 bg-slate-950/50 px-3 py-2">
      <div className="truncate text-[11px] uppercase text-slate-500">{label}</div>
      <div className="mt-1 text-sm font-semibold text-slate-100">{value}</div>
    </div>
  );
}

function ClosureTrend({ title, chart, metrics }: { title: string; chart: JsonMap; metrics: Array<{ key: string; label: string }> }) {
  const series = array(chart.series).map(record);
  if (!series.length) return null;
  return (
    <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div>
          <div className="text-sm font-semibold text-slate-100">{title}</div>
          <div className="mt-1 text-xs text-slate-500">
            {chart.baseline_only === true ? "Baseline only: no closure iteration artifact yet." : "Baseline and completed closure iterations."}
          </div>
        </div>
        <div className="text-xs text-slate-500">{chart.no_fake_iterations === true ? "real artifacts only" : ""}</div>
      </div>
      <div className="mt-4 overflow-x-auto">
        <div className="min-w-[720px]">
          <div className={`grid border-b border-slate-800 bg-slate-950/70 px-3 py-2 text-xs font-semibold uppercase text-slate-400`} style={{ gridTemplateColumns: `140px repeat(${metrics.length}, minmax(110px, 1fr))` }}>
            <div>Run</div>
            {metrics.map((metric) => <div key={metric.key}>{metric.label}</div>)}
          </div>
          {series.map((point, index) => (
            <div key={`${point.label || "run"}-${index}`} className="grid border-b border-slate-800 px-3 py-3 text-sm last:border-b-0" style={{ gridTemplateColumns: `140px repeat(${metrics.length}, minmax(110px, 1fr))` }}>
              <div className="font-semibold text-slate-100">{firstString(point.label, `iteration ${index}`)}</div>
              {metrics.map((metric) => (
                <div key={metric.key} className="break-words text-slate-300">{metricValue(point[metric.key])}</div>
              ))}
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}

export default function WorkflowEvidenceDashboard({ workflowId, status, stage, logs }: Props) {
  const [evidence, setEvidence] = useState<Record<string, JsonMap | null>>({});
  const [error, setError] = useState<string | null>(null);
  const [artifactsLoaded, setArtifactsLoaded] = useState(false);
  const flow = useMemo(() => displayedFlow(stage), [stage]);
  const stageIndex = flow.findIndex((item) => item.id === stage);
  const agentCount = useMemo(() => countParticipatingAgents(logs), [logs]);
  const resultsReady = hasTerminalEvidence(status, stage, logs);

  useEffect(() => {
    setArtifactsLoaded(false);
    setEvidence({});
    setError(null);
    if (!workflowId || !resultsReady) return;
    let active = true;
    const files: Record<Stage, string[]> = {
      arch2rtl: [
        "arch2rtl_dashboard.json",
        "digital/arch2rtl_dashboard.json",
        "digital_regmap.json",
        "upf_static_check.json",
        "digital/upf/upf_static_check.json",
        "digital/mbist_rtl_insertion/mbist_rtl_insertion_summary.json",
        "digital/mbist_rtl_insertion/mbist_integrated_rtl_lint.json",
        "digital/spec2rtl/spec2rtl_conformance.json",
        "system_rtl_dashboard.json",
        "system_rtl_package.json",
        "system_rtl_package_debug.json",
        "system_full_compile_summary.json",
        "system_integration_intent.json",
      ],
      dqa: [
        "rtl_lint_report.json",
        "cdc_findings.json",
        "reset_integrity_findings.json",
        "synthesis_readiness_findings.json",
        "dqa_summary.json",
        "tool_execution_summary.json",
        "tool_profile_used.json",
        "executive_summary.json",
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "digital/rtl_lint_report.json",
        "digital/cdc_findings.json",
        "digital/reset_integrity_findings.json",
        "signoff/synthesis_readiness_findings.json",
        "digital/dqa/dqa_summary.json",
        "digital/tool_execution_summary.json",
        "digital/tool_profile_used.json",
      ],
      smoke: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "simulation_manifest.json",
        "simulation_summary_coverage.json",
        "executive_summary.json",
      ],
      synthesis: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "handoff/MANIFEST.json",
        "implementation_setup_summary.json",
        "digital/synth/synth_summary.json",
        "digital/synth/metrics.json",
        "digital/synthesis_metrics.json",
        "digital/lec/lec_summary.json",
        "digital/synthesis_closure/synthesis_closure_plan.json",
        "digital/synthesis_closure/synthesis_closure_chart.json",
        "digital/post_dft_lec/post_dft_lec_summary.json",
        "upf_static_check.json",
        "digital/upf/upf_static_check.json",
        "scan_summary.json",
        "digital/dft/scan_summary.json",
        "atpg_summary.json",
        "digital/atpg/atpg_summary.json",
        "mbist_summary.json",
        "digital/mbist/mbist_summary.json",
        "synthesis_readiness_findings.json",
        "executive_summary.json",
      ],
      tapeout: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "handoff/MANIFEST.json",
        "implementation_setup_summary.json",
        "digital/synth/synth_summary.json",
        "digital/synth/metrics.json",
        "digital/synthesis_metrics.json",
        "digital/lec/lec_summary.json",
        "digital/synthesis_closure/synthesis_closure_plan.json",
        "digital/synthesis_closure/synthesis_closure_chart.json",
        "digital/post_dft_lec/post_dft_lec_summary.json",
        "upf_static_check.json",
        "digital/upf/upf_static_check.json",
        "scan_summary.json",
        "digital/dft/scan_summary.json",
        "atpg_summary.json",
        "digital/atpg/atpg_summary.json",
        "mbist_summary.json",
        "digital/mbist/mbist_summary.json",
        "floorplan_metrics.json",
        "floorplan_summary.json",
        "placement_metrics.json",
        "place_summary.json",
        "cts_summary.json",
        "sta_postroute_summary.json",
        "route_metrics.json",
        "route_summary.json",
        "fill_summary.json",
        "sta_postfill_summary.json",
        "analog/signoff/analog_signoff_summary.json",
        "drc_summary.json",
        "lvs_summary.json",
        "tapeout_package.json",
        "tapeout_summary.json",
        "tapeout_lec_summary.json",
        "digital/signoff_closure/signoff_closure_plan.json",
        "digital/signoff_closure/signoff_closure_chart.json",
        "executive_summary.json",
      ],
      verification: ["simulation_summary_coverage.json", "formal_report.json", "system_sim_dashboard.json"],
      embedded: [
        "system_firmware_dashboard.json",
        "system_firmware_execution.json",
        "system/firmware/cosim/system_firmware_dashboard.json",
        "system/firmware/cosim/system_firmware_execution.json",
        "system_firmware_coverage_dashboard.json",
        "system_firmware_coverage_summary.json",
        "system/firmware/coverage/system_firmware_coverage_dashboard.json",
        "system/firmware/coverage/system_firmware_coverage_summary.json",
      ],
      software: [
        "system_software_api_contract.json",
        "system/software/sdk/system_software_api_contract.json",
        "system_software_sdk_manifest.json",
        "system/software/sdk/system_software_sdk_manifest.json",
        "system_software_application_manifest.json",
        "system/software/apps/system_software_application_manifest.json",
        "system_software_build_manifest.json",
        "system/software/build/system_software_build_manifest.json",
        "system_software_test_manifest.json",
        "system/software/tests/system_software_test_manifest.json",
        "system_software_mock_manifest.json",
        "system/software/mock/system_software_mock_manifest.json",
        "system_software_executive_summary.json",
        "system/software/executive/system_software_executive_summary.json",
        "system_software_package.json",
        "system/software/package/system_software_package.json",
      ],
      validation: [
        "system_software_validation_summary_l2.json",
        "l2_validation_summary.json",
        "system/cosim/l2_validation_summary.json",
        "system/validation/l2/system_software_validation_summary_l2.json",
        "system/software_validation/cosim/summary/system_software_validation_summary_l2.json",
        "system_cosim_trace_validation_report.json",
        "system/validation/l2/system_cosim_trace_validation_report.json",
        "system/software_validation/cosim/trace/system_cosim_trace_validation_report.json",
        "system_cosim_execution_report.json",
        "system/validation/l2/system_cosim_execution_report.json",
        "system/software_validation/cosim/execution/system_cosim_execution_report.json",
        "system_cosim_harness_manifest.json",
        "system/validation/l2/system_cosim_harness_manifest.json",
        "system/software_validation/cosim/harness/system_cosim_harness_manifest.json",
        "system_software_validation_summary.json",
        "system/software_validation/system_software_validation_summary.json",
        "system/software_validation/summary/system_software_validation_summary.json",
        "build_validation_report.json",
        "system/software_validation/build/build_validation_report.json",
        "test_execution_report.json",
        "system/software_validation/test/test_execution_report.json",
        "mock_runtime_validation_report.json",
        "system/software_validation/mock/mock_runtime_validation_report.json",
        "package_audit_report.json",
        "system/software_validation/package/package_audit_report.json",
        "contract_consistency_report.json",
        "system/software_validation/contract/contract_consistency_report.json",
      ],
      product: [
        "system_product_dashboard_manifest.json",
        "system/product/app/system_product_dashboard_manifest.json",
        "system_product_package.json",
        "system/product/system_product_package.json",
        "system/product/package/system_product_package.json",
        "system_product_capability_model.json",
        "system/product/model/system_product_capability_model.json",
        "system_product_collateral_contract.json",
        "system/product/input/system_product_collateral_contract.json",
        "system/product/ingest/system_product_collateral_contract.json",
      ],
    };
    let timer: ReturnType<typeof setTimeout> | null = null;
    const loadArtifacts = (attempt: number) => {
      Promise.all((files[stage] || []).map(async (filename) => [filename.split("/").pop() || filename, await artifact(workflowId, filename)] as const))
        .then((entries) => {
        if (!active) return;
        const merged: Record<string, JsonMap | null> = {};
        for (const [key, value] of entries) {
          if (Object.keys(record(value)).length || !(key in merged)) {
            merged[key] = value;
          }
        }
        const hasEvidence = stageEvidenceReady(stage, merged);
        setEvidence(merged);
        setArtifactsLoaded(hasEvidence);
        if (!hasEvidence && attempt < 12) {
          timer = setTimeout(() => loadArtifacts(attempt + 1), 2500);
        }
        })
        .catch((reason: unknown) => {
          if (active) setError(reason instanceof Error ? reason.message : String(reason));
        });
    };
    loadArtifacts(0);
    return () => {
      active = false;
      if (timer) clearTimeout(timer);
    };
  }, [workflowId, stage, resultsReady]);

  const content = useMemo(() => {
    if (!workflowId || !resultsReady) {
      return <div className="mt-5 text-sm text-slate-400">Results appear after this stage completes.</div>;
    }
    if (error) return <div className="mt-5 text-sm text-amber-300">{error}</div>;
    if (!artifactsLoaded) {
      return (
        <div className="mt-5 rounded-lg border border-slate-800 bg-black/20 p-4 text-sm text-slate-400">
          Result artifacts are syncing. The dashboard will populate when the generated stage artifact is available.
        </div>
      );
    }

    if (stage === "arch2rtl") {
      const dashboard = record(evidence["arch2rtl_dashboard.json"]);
      if (Object.keys(dashboard).length) {
        const lint = record(dashboard.lint);
        const storage = record(dashboard.storage);
        const timing = record(dashboard.timing);
        const iface = record(dashboard.interface);
        const scopes = record(dashboard.scopes);
        const completePackage = record(scopes.complete_package);
        const clockReset = record(dashboard.clock_reset);
        const upf = record(evidence["upf_static_check.json"]);
        const spec2rtl = record(evidence["spec2rtl_conformance.json"]);
        const spec2rtlSummary = record(spec2rtl.summary);
        const mbistInsertion = record(evidence["mbist_rtl_insertion_summary.json"] || evidence["digital/mbist_rtl_insertion/mbist_rtl_insertion_summary.json"]);
        const mbistLint = record(evidence["mbist_integrated_rtl_lint.json"] || evidence["digital/mbist_rtl_insertion/mbist_integrated_rtl_lint.json"] || mbistInsertion.integrated_rtl_lint);
        const mbistSimulation = record(mbistInsertion.simulation);
        const mbistIverilog = record(mbistLint.iverilog);
        const mbistVerilator = record(mbistLint.verilator);
        const mbistLintFileCount = array(mbistLint.rtl_files).length;
        const hasMbistInsertion = Object.keys(mbistInsertion).length > 0;
        const hasMbistLint = Object.keys(mbistLint).length > 0;
        const mbistLintPass = firstString(mbistIverilog.status) === "pass" && firstString(mbistVerilator.status) === "pass";
        const mbistSimulationPass = firstString(mbistSimulation.status) === "pass";
        const hasSpec2Rtl = Object.keys(spec2rtl).length > 0;
        const hasUpf = Object.keys(upf).length > 0;
        const lintStatus = firstString(lint.status, "unavailable");
        return (
          <div className="mt-5 grid gap-5 xl:grid-cols-[minmax(280px,0.6fr)_minmax(0,1.4fr)]">
            <div className="space-y-3">
              <Bar label="Input bits" value={number(iface.input_count)} total={Math.max(number(iface.input_count) + number(iface.output_count), 1)} color="bg-cyan-500" />
              <Bar label="Output bits" value={number(iface.output_count)} total={Math.max(number(iface.input_count) + number(iface.output_count), 1)} color="bg-emerald-500" />
              <Bar label="Flip-flops" value={number(storage.flipflop_count)} total={Math.max(number(storage.flipflop_count) + number(storage.latch_count), 1)} color="bg-violet-500" />
              <Bar label="Latches" value={number(storage.latch_count)} total={Math.max(number(storage.flipflop_count) + number(storage.latch_count), 1)} color="bg-amber-500" />
              <div className="grid grid-cols-2 gap-2 pt-2">
                <MiniMetric label="Input Ports" value={number(iface.input_port_count)} />
                <MiniMetric label="Output Ports" value={number(iface.output_port_count)} />
                <MiniMetric label="Functional RTL" value={number(dashboard.rtl_file_count)} />
                <MiniMetric label="Functional Modules" value={number(dashboard.module_count)} />
                <MiniMetric label="Full-Cycle" value={number(timing.full_cycle_path_count)} />
                <MiniMetric label="Half-Cycle" value={number(timing.half_cycle_path_count)} />
              </div>
            </div>
            <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-3 2xl:grid-cols-4">
              <Stat title="Lint" value={lintStatus} />
              <Stat title="Clock" value={firstString(clockReset.primary_clock, "not inferred")} />
              <Stat title="Reset" value={firstString(clockReset.primary_reset, "not inferred")} />
              {hasUpf ? <Stat title="UPF Static" value={statusLabel(upf.status)} /> : null}
              {hasUpf ? <Stat title="Power Domains" value={metricValue(upf.domain_count)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST RTL" value={statusLabel(mbistInsertion.status)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST Standalone Sim" value={mbistSimulationPass ? "pass" : statusLabel(mbistSimulation.status)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST Algorithm" value={metricValue(mbistInsertion.algorithm)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST RAMs" value={metricValue(mbistInsertion.ram_count, mbistInsertion.memory_count)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST Controllers" value={metricValue(mbistInsertion.mbist_controller_count)} /> : null}
              {hasMbistInsertion ? <Stat title="MBIST Wrappers" value={metricValue(mbistInsertion.wrapper_module_count)} /> : null}
              {hasMbistInsertion ? <Stat title="Package RTL Files" value={metricValue(completePackage.rtl_file_count)} /> : null}
              {hasMbistInsertion ? <Stat title="Package Modules" value={metricValue(completePackage.module_count)} /> : null}
              {number(storage.memory_bit_count) ? <Stat title="Behavioral Memory Bits" value={metricValue(storage.memory_bit_count)} /> : null}
              {hasMbistLint ? <Stat title="Integrated MBIST RTL Lint" value={mbistLintPass ? "pass" : "fail"} /> : null}
              {hasMbistLint ? <Stat title="Integrated RTL Files Linted" value={metricValue(mbistLintFileCount)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL" value={statusLabel(spec2rtl.status)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Checked" value={metricValue(spec2rtlSummary.checked)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Matched" value={metricValue(spec2rtlSummary.matched)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Partial" value={metricValue(spec2rtlSummary.partial)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Missing" value={metricValue(spec2rtlSummary.missing)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Inconclusive" value={metricValue(spec2rtlSummary.inconclusive)} /> : null}
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            </div>
          </div>
        );
      }
      const registers = array(record(evidence["digital_regmap.json"]?.regmap).registers);
      const systemDashboard = record(evidence["system_rtl_dashboard.json"]);
      if (Object.keys(systemDashboard).length) {
        const compileSummary = record(evidence["system_full_compile_summary.json"]);
        const simCompile = record(compileSummary.sim);
        const simTools = record(simCompile.tools);
        const compileTool = firstString(simTools.compile, "iverilog");
        const lintTool = firstString(simTools.lint, "verilator");
        const simIverilog = firstPresent(simCompile.iverilog_ok_pass2, simCompile.iverilog_ok_pass1);
        const simVerilator = firstPresent(simCompile.verilator_ok_pass2, simCompile.verilator_ok_pass1);
        const toolDetail = `compile ${simIverilog === true ? "pass" : simIverilog === false ? "fail" : "not run"}, lint ${simVerilator === true ? "pass" : simVerilator === false ? "fail" : "not run"}`;
        const scopes = record(systemDashboard.scopes);
        const compile = record(systemDashboard.compile);
        const systemScope = record(scopes.system);
        const digitalScope = record(scopes.digital);
        const analogScope = record(scopes.analog);
        const socScope = record(scopes.soc);
        const lintSummary = record(systemDashboard.lint_summary);
        const iface = record(socScope.interface);
        const storage = record(systemScope.storage);
        const timing = record(systemScope.timing);
        const clockReset = record(socScope.clock_reset);
        const spec2rtl = record(evidence["spec2rtl_conformance.json"]);
        const spec2rtlSummary = record(spec2rtl.summary);
        const hasSpec2Rtl = Object.keys(spec2rtl).length > 0;
        const bitTotal = Math.max(number(iface.input_count) + number(iface.output_count), 1);
        const portTotal = Math.max(number(iface.input_port_count) + number(iface.output_port_count), 1);
        const storageTotal = Math.max(number(storage.flipflop_count) + number(storage.latch_count), 1);
        const rtlFileTotal = Math.max(number(systemScope.rtl_file_count), 1);
        const participatedTotal = Math.max(agentCount ?? 0, 1);
        const physCompile = firstString(compile.phys);
        return (
          <div className="mt-5 grid gap-5 2xl:grid-cols-[minmax(0,0.8fr)_minmax(0,1.2fr)]">
            <div className="2xl:col-span-2">
              <ToolStrip used={[compileTool, lintTool]} defaultTool={`${compileTool} / ${lintTool}`} />
            </div>
            <div className="space-y-3">
              <Bar label="SoC input bits" value={number(iface.input_count)} total={bitTotal} color="bg-cyan-500" />
              <Bar label="SoC output bits" value={number(iface.output_count)} total={bitTotal} color="bg-emerald-500" />
              <Bar label="SoC input ports" value={number(iface.input_port_count)} total={portTotal} color="bg-sky-500" />
              <Bar label="SoC output ports" value={number(iface.output_port_count)} total={portTotal} color="bg-teal-500" />
              <Bar label="System flip-flops" value={number(storage.flipflop_count)} total={storageTotal} color="bg-violet-500" />
              <Bar label="System latches" value={number(storage.latch_count)} total={storageTotal} color="bg-amber-500" />
              <Bar label="RTL files" value={number(systemScope.rtl_file_count)} total={rtlFileTotal} color="bg-indigo-500" />
              <Bar label="Digital RTL files" value={number(digitalScope.rtl_file_count)} total={rtlFileTotal} color="bg-blue-500" />
              <Bar label="Analog RTL files" value={number(analogScope.rtl_file_count)} total={rtlFileTotal} color="bg-rose-500" />
              <Bar label="SoC RTL files" value={number(socScope.rtl_file_count)} total={rtlFileTotal} color="bg-fuchsia-500" />
              {agentCount !== null ? <Bar label="Agents participated" value={agentCount} total={participatedTotal} color="bg-slate-400" /> : null}
            </div>
            <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 2xl:grid-cols-3">
              <CheckCard title="Digital Lint" status={firstString(lintSummary.digital, record(digitalScope.lint).status, "not run")} tool="verilator" />
              <CheckCard title="Analog Lint" status={firstString(lintSummary.analog, record(analogScope.lint).status, "not run")} tool="verilator" detail="behavioral model lint" />
              <CheckCard title="SoC Lint" status={firstString(lintSummary.soc, compile.sim, "not produced")} tool={`${compileTool} / ${lintTool}`} detail={toolDetail} />
              <CheckCard title="System Lint" status={firstString(lintSummary.system, record(systemScope.lint).status, "not run")} tool={`${compileTool} / ${lintTool}`} detail="Digital + analog + SoC roll-up" />
              <Stat title="Full-cycle Paths" value={number(timing.full_cycle_path_count)} />
              <Stat title="Half-cycle Paths" value={number(timing.half_cycle_path_count)} />
              <Stat title="Clock" value={firstString(clockReset.primary_clock, "not inferred")} />
              <Stat title="Reset" value={firstString(clockReset.primary_reset, "not inferred")} />
              <Stat title="Modules" value={number(systemScope.module_count)} />
              {physCompile && physCompile !== "skipped" ? <Stat title="Physical RTL Compile" value={physCompile} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL" value={statusLabel(spec2rtl.status)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Checked" value={metricValue(spec2rtlSummary.checked)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Matched" value={metricValue(spec2rtlSummary.matched)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Partial" value={metricValue(spec2rtlSummary.partial)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Missing" value={metricValue(spec2rtlSummary.missing)} /> : null}
              {hasSpec2Rtl ? <Stat title="Spec2RTL Inconclusive" value={metricValue(spec2rtlSummary.inconclusive)} /> : null}
            </div>
          </div>
        );
      }
      const systemPkg = record(evidence["system_rtl_package.json"]);
      const systemDebug = record(evidence["system_rtl_package_debug.json"]);
      const compile = record(evidence["system_full_compile_summary.json"]);
      const intent = record(evidence["system_integration_intent.json"]);
      if (Object.keys(systemPkg).length || Object.keys(systemDebug).length || Object.keys(intent).length) {
        const filelists = record(systemPkg.filelists);
        const compileInfo = record(systemPkg.compile);
        const top = record(systemPkg.top);
        const simFiles = array(filelists.sim);
        const physFiles = array(filelists.phys);
        const instances = array(intent.instances);
        const connections = array(intent.connections);
        const artifacts = record(systemPkg.artifacts);
        return (
          <div className="mt-5 space-y-5">
            <div className="grid gap-3 sm:grid-cols-2">
              <Bar label="RTL files imported" value={simFiles.length || physFiles.length} total={Math.max(simFiles.length || physFiles.length, 1)} color="bg-cyan-500" />
              <Bar label="Integration instances" value={instances.length} total={Math.max(instances.length, 1)} color="bg-violet-500" />
            </div>
            <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
              <Stat title="Top Module" value={firstString(top.sim, top.phys, "soc_top_sim")} />
              <Stat title="RTL Files" value={simFiles.length || physFiles.length} />
              <Stat title="Input Bits" value="not produced pre-synthesis" />
              <Stat title="Output Bits" value="not produced pre-synthesis" />
              <Stat title="Flip-flops" value="not produced pre-synthesis" />
              <Stat title="Latches" value="not produced pre-synthesis" />
              <Stat title="Full-cycle Paths" value="not produced pre-synthesis" />
              <Stat title="Half-cycle Paths" value="not produced pre-synthesis" />
              <Stat title="SoC Lint" value={firstString(compileInfo.sim, record(compile.sim).status, "not produced")} />
              <Stat title="Physical Lint" value={firstString(compileInfo.phys, record(compile.phys).status, "not produced")} />
              <Stat title="Instances" value={instances.length} />
              <Stat title="Connections" value={connections.length} />
              <Stat title="Analog Macro" value={artifacts.integration_intent ? "integrated by intent" : "not reported"} />
              <Stat title="Ready for Cosim" value={systemPkg.ready_for_cosim === true ? "yes" : "no"} />
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            </div>
          </div>
        );
      }
      return registers.length ? (
        <div className="mt-5">
          <div className="text-sm font-semibold text-slate-100">Generated Firmware Register Interface</div>
          <div className="mt-3 grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            {registers.slice(0, 8).map((item, index) => {
              const register = record(item);
              return (
                <div key={`${String(register.name || "register")}-${index}`} className="min-w-0 rounded-lg border border-cyan-900/60 bg-cyan-950/15 p-3">
                  <div className="break-all text-xs text-cyan-300">{String(register.offset || "-")}</div>
                  <div className="mt-1 break-words font-semibold text-slate-100">{String(register.name || "REGISTER")}</div>
                  <div className="mt-1 break-words text-xs text-slate-400">{String(register.access || "")}</div>
                </div>
              );
            })}
          </div>
        </div>
      ) : <div className="mt-5 text-sm text-amber-300">Register-map artifact is not available for this completed run.</div>;
    }

    if (stage === "dqa") {
      const handoff = record(evidence["rtl_handoff_ingest_manifest.json"]);
      const lint = record(evidence["rtl_lint_report.json"]);
      const cdc = record(evidence["cdc_findings.json"]);
      const reset = record(evidence["reset_integrity_findings.json"]);
      const readiness = record(evidence["synthesis_readiness_findings.json"]);
      const summary = record(evidence["dqa_summary.json"] || evidence["executive_summary.json"]);
      const toolSummary = dqaToolSummary(
        lint,
        readiness,
        record(evidence["tool_execution_summary.json"]),
        record(evidence["tool_profile_used.json"])
      );
      const lintExecution = record(array(record(lint.tooling).executions)[0]);
      const lintTool = firstString(lintExecution.tool, "verilator");
      const synthTool = record(readiness.yosys).available === true ? "yosys" : "not available";
      const readinessScore = firstPresent(readiness.score);
      const yosysErrors = array(record(readiness.yosys).errors).length;
      const checkRows = [
        { check: "RTL Lint", status: lintVerdict(lint), detail: `${findingCount(lint)} findings`, tool: lintTool },
        { check: "CDC", status: findingsVerdict(cdc), detail: `${findingCount(cdc)} findings`, tool: "heuristic scan" },
        { check: "Reset", status: findingsVerdict(reset), detail: `${findingCount(reset)} findings`, tool: "heuristic scan" },
        {
          check: "Synth Ready",
          status: synthesisReadinessVerdict(readiness),
          detail: readinessScore !== undefined ? `score ${String(readinessScore)}${yosysErrors ? `, ${yosysErrors} yosys error(s)` : ""}` : "not produced",
          tool: synthTool,
        },
      ];
      const rtlFiles = firstNumber(
        summary.rtl_file_count,
        handoff.rtl_file_count,
        array(handoff.rtl_files).length
      );
      return (
        <div className="mt-5 space-y-5">
          <ToolStrip used={toolSummary.used} defaultTool={toolSummary.defaultTool} />
          <div className="grid gap-3 sm:grid-cols-1">
            <Bar label="RTL files imported" value={rtlFiles} total={Math.max(rtlFiles, 1)} color="bg-cyan-500" />
          </div>
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            {checkRows.map((row) => (
              <CheckCard key={row.check} title={row.check} status={row.status} detail={row.detail} />
            ))}
          </div>
          <CheckTable rows={checkRows} />
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            <Stat title="Source" value={firstString(handoff.source_mode, "imported").replaceAll("_", " ")} />
            <Stat title="RTL Files" value={rtlFiles} />
            <Stat title="Top Module" value={firstString(handoff.top_module, "not inferred")} />
            <Stat title="Findings" value={findingCount(lint) + findingCount(cdc) + findingCount(reset) + findingCount(readiness)} />
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Summary" value={firstString(summary.status, summary.verdict, status || "running")} />
          </div>
        </div>
      );
    }

    if (stage === "smoke") {
      const handoff = record(evidence["rtl_handoff_ingest_manifest.json"]);
      const sim = record(record(evidence["simulation_summary_coverage.json"]).simulation);
      const summary = record(evidence["executive_summary.json"]);
      const rtlFiles = firstNumber(handoff.rtl_file_count, array(handoff.rtl_files).length);
      const passed = firstNumber(sim.pass, sim.passed);
      const failed = firstNumber(sim.fail, sim.failed);
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-3 sm:grid-cols-3">
            <Bar label="RTL files imported" value={rtlFiles} total={Math.max(rtlFiles, 1)} color="bg-cyan-500" />
            <Bar label="Simulation passed" value={passed} total={Math.max(passed + failed, 1)} color="bg-emerald-500" />
            <Bar label="Simulation failed" value={failed} total={Math.max(passed + failed, 1)} color="bg-rose-500" />
          </div>
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            <Stat title="Source" value={firstString(handoff.source_mode, "imported").replaceAll("_", " ")} />
            <Stat title="RTL Files" value={rtlFiles} />
            <Stat title="Top Module" value={firstString(handoff.top_module, "not inferred")} />
            <Stat title="Runs" value={firstNumber(sim.total, passed + failed)} />
            <Stat title="Simulation" value={failed > 0 ? "fail" : passed > 0 ? "pass" : "not run"} />
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Summary" value={firstString(summary.status, summary.verdict, status || "running")} />
          </div>
        </div>
      );
    }

    if (stage === "synthesis" || stage === "tapeout") {
      const handoff = record(evidence["rtl_handoff_ingest_manifest.json"]);
      const systemDashboard = record(evidence["system_rtl_dashboard.json"]);
      const systemDashboardFilelists = record(systemDashboard.filelists);
      const systemDashboardScopes = record(systemDashboard.scopes);
      const systemDashboardSystemScope = record(systemDashboardScopes.system);
      const setup = record(evidence["implementation_setup_summary.json"]);
      const synthSummary = record(evidence["synth_summary.json"]);
      const synthInputs = record(synthSummary.inputs);
      const synth = record(evidence["metrics.json"] || evidence["synthesis_metrics.json"]);
      const lec = record(evidence["lec_summary.json"]);
      const synthesisClosureChart = record(evidence["synthesis_closure_chart.json"]);
      const upf = record(evidence["upf_static_check.json"]);
      const hasUpf = Object.keys(upf).length > 0;
      const dft = record(evidence["scan_summary.json"]);
      const postDftLec = record(evidence["post_dft_lec_summary.json"]);
      const atpg = record(evidence["atpg_summary.json"]);
      const mbist = record(evidence["mbist_summary.json"]);
      const floorplan = record(evidence["floorplan_summary.json"]);
      const place = record(evidence["place_summary.json"]);
      const cts = record(evidence["cts_summary.json"]);
      const route = record(evidence["route_summary.json"]);
      const fill = record(evidence["fill_summary.json"]);
      const drcSummary = record(evidence["drc_summary.json"]);
      const lvsSummary = record(evidence["lvs_summary.json"]);
      const analogSignoff = record(evidence["analog_signoff_summary.json"]);
      const analogDrc = record(analogSignoff.drc);
      const analogLvs = record(analogSignoff.lvs);
      const analogXor = record(analogSignoff.xor);
      const tapeoutSummary = record(evidence["tapeout_summary.json"]);
      const tapeoutLec = record(evidence["tapeout_lec_summary.json"]);
      const signoffClosure = record(evidence["signoff_closure_plan.json"]);
      const signoffClosureChart = record(evidence["signoff_closure_chart.json"]);
      const summary = record(evidence["executive_summary.json"]);
      const staStages = record(summary.sta_stages);
      const postfill = record(staStages.sta_postfill);
      const postroute = record(staStages.sta_postroute);
      const postcts = record(staStages.sta_postcts);
      const postplace = record(staStages.sta_postplace);
      const preplace = record(staStages.sta_preplace);
      const wns = firstPresent(
        summary.worst_slack,
        postfill.worst_slack,
        postroute.worst_slack,
        postcts.worst_slack,
        postplace.worst_slack,
        preplace.worst_slack,
        synth.chiploop__sta_preplace_wns,
        synth.worst_slack,
        synth.timing__setup__ws
      );
      const tns = firstPresent(
        summary.tns,
        postfill.tns,
        postroute.tns,
        postcts.tns,
        postplace.tns,
        preplace.tns,
        synth.chiploop__sta_preplace_tns,
        synth.tns,
        synth.timing__setup__tns
      );
      const postfillSummary = record(evidence["sta_postfill_summary.json"]);
      const postfillStatus = firstString(postfillSummary.status, postfill.status);
      const postfillSetupWns = firstPresent(postfill.setup_wns, postfill.timing__setup__wns, postfill.timing__setup__ws, postfill.worst_slack, postfillSummary.setup_wns, postfillSummary.worst_slack);
      const postfillSetupTns = firstPresent(postfill.setup_tns, postfill.timing__setup__tns, postfill.tns, postfillSummary.setup_tns, postfillSummary.tns);
      const postfillHoldWns = firstPresent(postfill.hold_wns, postfill.timing__hold__wns, postfill.timing__hold__ws, postfillSummary.hold_wns);
      const postfillHoldTns = firstPresent(postfill.hold_tns, postfill.timing__hold__tns, postfillSummary.hold_tns);
      const postfillSetupViolations = zeroWhenClean(postfillStatus, firstPresent(
        postfill.setup_violations,
        postfill.timing__setup__violation_count,
        postfill.timing__setup__vio__count,
        postfill.timing__setup_vio__count,
        postfill.timing__setup_r2r_vio__count,
        postfillSummary.setup_violations
      ));
      const postfillHoldViolations = zeroWhenClean(postfillStatus, firstPresent(
        postfill.hold_violations,
        postfill.timing__hold__violation_count,
        postfill.timing__hold__vio__count,
        postfill.timing__hold_vio__count,
        postfill.timing__hold_r2r_vio__count,
        postfillSummary.hold_violations
      ));
      const area = metricValue(summary.area, synth.area, synth.design__instance__area, synth.design__core__area);
      const cells = metricValue(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count);
      const flipflops = metricValue(summary.flipflop_count, synth.chiploop__flipflop_count, synth.flipflops, synth.ff_count, synth.registers, synth.design__instance__ff_count, synth["design__instance__count:flop"]);
      const latches = metricValue(summary.latch_count, synth.chiploop__latch_count, synth.latches, synth.latch_count, synth.design__instance__latch_count);
      const unmapped = metricValue(synth.chiploop__unmapped_cell_count, synth.design__instance_unmapped__count);
      const checkErrors = metricValue(synth.chiploop__synthesis_check_error_count, synth.synthesis__check_error__count);
      const netlistStatus = synth.chiploop__netlist_present === true || firstString(record(synthSummary.outputs).netlist) ? "generated" : "not produced";
      const timingViolations = timingViolationValue(
        wns,
        tns,
        firstPresent(
          synth.chiploop__sta_preplace_setup_violation_count,
          synth.timing_violations,
          synth.setup_violations,
          synth.timing__setup__vio__count,
          synth.timing__setup_vio__count,
          synth.timing__setup__violation__count,
          synth.timing__setup__violating_paths,
          synth.sta__setup__violation_count
        )
      );
      const rtlFiles = Math.max(
        firstNumber(handoff.rtl_file_count),
        array(handoff.rtl_files).length,
        array(synthInputs.rtl_files).length,
        firstNumber(systemDashboardFilelists.sim_count),
        firstNumber(systemDashboardFilelists.phys_count),
        firstNumber(systemDashboardSystemScope.rtl_file_count)
      );
      const drc = metricValue(
        summary.drc_violations,
        record(evidence["route_metrics.json"]).drc_violations,
        drcSummary.drc_violations,
        drcSummary.violations,
        drcSummary.drc_status,
        firstString(drcSummary.status) ? statusLabel(drcSummary.status) : undefined
      );
      const lvs = metricValue(
        summary.lvs_status,
        lvsSummary.lvs_status,
        firstString(lvsSummary.status) ? statusLabel(lvsSummary.status) : undefined
      );
      const tapeoutSignoff = record(tapeoutSummary.signoff_inputs);
      const xor = firstString(tapeoutSignoff.xor_status, tapeoutSummary.xor_status) === "not_applicable"
        ? "not applicable"
        : metricValue(tapeoutSignoff.xor_differences, tapeoutSummary.xor_differences, drcSummary.xor_differences, lvsSummary.xor_differences);
      const overall = stage === "tapeout" ? firstString(tapeoutSummary.status, summary.status, summary.verdict, status || "running") : firstString(summary.status, summary.verdict, synthSummary.status, status || "running");
      const usedTools = uniqueStrings([
        firstString(synthSummary.tool),
        firstString(lec.tool),
        firstString(dft.tool),
        firstString(postDftLec.tool),
        firstString(atpg.tool),
        firstString(floorplan.tool),
        firstString(place.tool),
        firstString(cts.tool),
        firstString(route.tool),
        firstString(fill.tool),
        firstString(drcSummary.tool),
        firstString(lvsSummary.tool),
        firstString(tapeoutSummary.tool),
        firstString(tapeoutLec.tool),
      ]);
      return (
        <div className="mt-5 space-y-5">
          <ToolStrip used={usedTools} defaultTool={usedTools.join(" / ") || "not reported"} />
          <ClosureTrend
            title="Synthesis Closure Trend"
            chart={synthesisClosureChart}
            metrics={[
              { key: "wns", label: "WNS" },
              { key: "tns", label: "TNS" },
              { key: "setup_violations", label: "Setup Vios" },
              { key: "lec_status", label: "LEC" },
              { key: "lec_unproven_points", label: "LEC Unproven" },
              { key: "post_dft_lec_status", label: "Post-DFT LEC" },
              { key: "post_dft_lec_unproven_points", label: "Post-DFT Unproven" },
            ]}
          />
          {stage === "tapeout" ? (
            <ClosureTrend
              title="PD Signoff Closure Trend"
              chart={signoffClosureChart}
              metrics={[
                { key: "postfill_wns", label: "PostFill WNS" },
                { key: "postfill_tns", label: "PostFill TNS" },
                { key: "postfill_setup_wns", label: "Setup WNS" },
                { key: "postfill_setup_tns", label: "Setup TNS" },
                { key: "postfill_hold_wns", label: "Hold WNS" },
                { key: "postfill_hold_tns", label: "Hold TNS" },
                { key: "postfill_setup_violations", label: "Setup Vios" },
                { key: "postfill_hold_violations", label: "Hold Vios" },
                { key: "drc_violations", label: "DRC" },
                { key: "lvs_status", label: "LVS" },
                { key: "tapeout_lec_status", label: "Tapeout LEC" },
              ]}
            />
          ) : null}
          <div className="grid gap-3 sm:grid-cols-2">
            <Bar label="RTL files imported" value={rtlFiles} total={Math.max(rtlFiles, 1)} color="bg-cyan-500" />
            <Bar label="Leaf cells" value={typeof cells === "number" ? cells : firstNumber(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count)} total={Math.max(firstNumber(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count), 1)} color="bg-violet-500" />
          </div>
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            <Stat title="Source" value={firstString(handoff.source_mode, "imported").replaceAll("_", " ")} />
            <Stat title="Top Module" value={firstString(synthInputs.top_module, handoff.top_module, summary.design_name, "not inferred")} />
            <Stat title="RTL Files" value={rtlFiles} />
            <Stat title="SDC Checks" value={sdcStatus(setup, synthSummary)} />
            <Stat title="Synthesis" value={synthesisStatus(synthSummary)} />
            <Stat title="Area (um^2)" value={area} />
            <Stat title="Leaf Cells" value={cells} />
            <Stat title="Flip-flops" value={flipflops} />
            <Stat title="Latches" value={latches} />
            <Stat title="WNS (ns)" value={signedMetric(wns)} />
            <Stat title="TNS (ns)" value={signedMetric(tns)} />
            <Stat title="Timing Violations" value={timingViolations} />
            <Stat title="Unmapped Cells" value={unmapped} />
            <Stat title="Synthesis Errors" value={checkErrors} />
            <Stat title="Netlist" value={netlistStatus} />
            <Stat title={stage === "tapeout" ? "Synthesis LEC" : "LEC"} value={lecDashboardStatus(lec)} />
            <Stat title={stage === "tapeout" ? "Synthesis LEC Unproven" : "LEC Unproven"} value={unprovenMetric(lec.status, lec.unproven_points)} />
            {stage === "tapeout" ? <Stat title="Tapeout LEC" value={lecDashboardStatus(tapeoutLec)} /> : null}
            {stage === "tapeout" ? <Stat title="Tapeout LEC Unproven" value={unprovenMetric(tapeoutLec.status, tapeoutLec.unproven_points)} /> : null}
            {hasUpf ? <Stat title="UPF Static" value={statusLabel(upf.status)} /> : null}
            {hasUpf ? <Stat title="Power Domains" value={metricValue(upf.domain_count)} /> : null}
            {hasUpf ? <Stat title="Isolation Rules" value={metricValue(upf.isolation_rule_count)} /> : null}
            {hasUpf ? <Stat title="Retention Rules" value={metricValue(upf.retention_rule_count)} /> : null}
            <Stat title="DFT" value={dftDashboardStatus(dft)} />
            <Stat title="Post-DFT LEC" value={lecDashboardStatus(postDftLec)} />
            <Stat title="Post-DFT LEC Unproven" value={unprovenMetric(postDftLec.status, postDftLec.unproven_points)} />
            <Stat title="Scan Chains" value={scanMetric(dft.status, firstPresent(dft.actual_scan_chains, dft.scan_chains))} />
            <Stat title="Scan Candidates" value={metricValue(dft.scan_flops)} />
            <Stat title="ATPG" value={atpgDashboardStatus(atpg)} />
            <Stat title="ATPG Patterns" value={atpgMetric(atpg.status, atpg.pattern_count)} />
            <Stat title="Stuck-at Coverage" value={atpgMetric(atpg.status, atpg.stuck_at_coverage_pct)} />
            <Stat title="MBIST" value={statusLabel(mbist.status)} />
            <Stat title="Memories" value={metricValue(mbist.memory_count)} />
            <Stat title="Memory Bits" value={metricValue(mbist.estimated_memory_bits)} />
            <Stat title="RTL Storage Arrays" value={metricValue(mbist.non_mbist_storage_count)} />
            <Stat title="autombist" value={mbist.autombist_available === true ? "available" : mbist.autombist_available === false ? "not configured" : "not produced"} />
            {stage === "tapeout" ? <Stat title="Floorplan" value={statusLabel(floorplan.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Place" value={statusLabel(place.status)} /> : null}
            {stage === "tapeout" ? <Stat title="CTS" value={statusLabel(cts.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Route" value={statusLabel(route.status)} /> : null}
            {stage === "tapeout" ? <Stat title="PostRoute STA" value={statusLabel(record(evidence["sta_postroute_summary.json"]).status || postroute.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Fill" value={statusLabel(fill.status)} /> : null}
            {stage === "tapeout" ? <Stat title="PostFill STA" value={statusLabel(postfillStatus)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Setup WNS" value={signedMetric(postfillSetupWns)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Setup TNS" value={signedMetric(postfillSetupTns)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Hold WNS" value={signedMetric(postfillHoldWns)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Hold TNS" value={signedMetric(postfillHoldTns)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Setup Violations" value={metricValue(postfillSetupViolations)} /> : null}
            {stage === "tapeout" && Object.keys(postfill).length ? <Stat title="PostFill Hold Violations" value={metricValue(postfillHoldViolations)} /> : null}
            {stage === "tapeout" && Object.keys(analogSignoff).length ? <Stat title="Analog DRC" value={statusLabel(analogDrc.status)} /> : null}
            {stage === "tapeout" && Object.keys(analogSignoff).length ? <Stat title="Analog DRC Issues" value={metricValue(analogDrc.feedback_problem_count)} /> : null}
            {stage === "tapeout" && Object.keys(analogSignoff).length ? <Stat title="Analog LVS" value={statusLabel(analogLvs.status)} /> : null}
            {stage === "tapeout" && Object.keys(analogSignoff).length ? <Stat title="Analog XOR" value={statusLabel(analogXor.status)} /> : null}
            {stage === "tapeout" ? <Stat title="DRC Violations" value={drc} /> : null}
            {stage === "tapeout" ? <Stat title="LVS" value={lvs} /> : null}
            {stage === "tapeout" ? <Stat title="XOR Differences" value={xor} /> : null}
            {stage === "tapeout" ? <Stat title="Tapeout" value={statusLabel(tapeoutSummary.status)} /> : null}
            {stage === "tapeout" && Object.keys(signoffClosure).length ? <Stat title="Closure Loop" value={statusLabel(signoffClosure.status || signoffClosure.stop_reason)} /> : null}
            {stage === "tapeout" && Object.keys(signoffClosure).length ? <Stat title="Closure Restart" value={firstString(signoffClosure.selected_restart_stage, "none")} /> : null}
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Summary" value={statusLabel(overall)} />
          </div>
        </div>
      );
    }

    if (stage === "verification") {
      const verifyDashboard = evidence["simulation_summary_coverage.json"] || evidence["system_sim_dashboard.json"] || {};
      const simulation = record(verifyDashboard?.simulation);
      const coverage = record(verifyDashboard?.coverage);
      const codeCoverage = record(coverage.code);
      const assertionCoverage = record(coverage.assertions);
      const formalReport = record(evidence["formal_report.json"]);
      const formal = record(verifyDashboard?.formal);
      const golden = record(verifyDashboard?.golden_model);
      const toolchain = record(verifyDashboard?.toolchain);
      const passed = number(simulation.pass);
      const failed = number(simulation.fail);
      const total = number(simulation.total);
      const codeStatus = String(codeCoverage.status || "");
      const formalStatus = String(formal.status || formalReport.status || "not_enabled");
      const formalValue = formalStatus === "fail" && typeof formal.returncode === "number"
        ? `fail (rc ${formal.returncode})`
        : formalStatus;
      const toolsValue = [
        String(toolchain.simulator || "verilator"),
        String(toolchain.code_coverage || ""),
        String(toolchain.formal || ""),
      ].filter(Boolean).join(" / ");
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-3 sm:grid-cols-2">
            <Bar label="Simulation passed" value={passed} total={total} color="bg-emerald-500" />
            <Bar label="Simulation failed" value={failed} total={total} color="bg-rose-500" />
          </div>
          <div className="grid min-w-0 grid-cols-2 gap-3">
            <Stat title="Runs" value={total} />
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Functional Coverage" value={pct(coverage.functional_coverage_pct)} />
            <Stat title="Code Line" value={pctWithStatus(codeCoverage.line_coverage_pct, codeStatus)} />
            <Stat title="Code Branch" value={pctWithStatus(codeCoverage.branch_coverage_pct, codeStatus)} />
            <Stat title="Code Condition" value={pctWithStatus(codeCoverage.condition_coverage_pct, codeCoverage.condition_source || codeStatus)} />
            <Stat title="Code Toggle" value={pctWithStatus(codeCoverage.toggle_coverage_pct, codeCoverage.toggle_source || codeStatus)} />
            <Stat title="SVA Assertion Coverage" value={pct(assertionCoverage.assertion_pass_pct)} />
            <Stat title="Formal" value={statusLabel(formalValue)} />
            <Stat title="Golden Model" value={statusLabel(golden.status)} />
            <div className="col-span-2">
              <Stat title="Tools" value={toolsValue || "verilator"} />
            </div>
          </div>
          {codeCoverage.toggle_source === "not_reported_by_verilator_lcov" || codeCoverage.toggle_source === "not_reported_by_verilator_annotate_points" ? (
            <div className="text-xs text-slate-500">
              Toggle coverage was not present in this run&apos;s Verilator coverage artifacts. New backend runs collect annotated toggle points when Verilator provides them.
            </div>
          ) : null}
        </div>
      );
    }

    if (stage === "embedded") {
      const dashboard = evidence["system_firmware_dashboard.json"] || evidence["system_firmware_coverage_dashboard.json"] || {};
      const execution = evidence["system_firmware_execution.json"] || evidence["system_firmware_coverage_summary.json"] || {};
      const readiness = record(execution.readiness);
      const inputs = record(execution.inputs);
      const results = record(execution.results);
      const missingInputs = array(dashboard.missing_inputs).length
        ? array(dashboard.missing_inputs).map(String)
        : array(readiness.missing).map(String);
      const firmwareElfPlaceholder = dashboard.firmware_elf_placeholder === true || inputs.firmware_elf_placeholder === true;
      const testMatrix = array(execution.test_matrix);
      const passed = firstNumber(dashboard.passed_test_count, results.passed_test_count);
      const failed = firstNumber(dashboard.failed_test_count, results.failed_test_count);
      const executed = firstNumber(dashboard.executed_test_count, results.executed_test_count);
      const planned = firstNumber(dashboard.planned_test_count, testMatrix.length);
      const attempted = results.attempted === true || executed > 0;
      const runtimeRequested = results.runtime_requested === true;
      const runtimeCapable = results.runtime_capable === true;
      const executionMode = firstString(execution.execution_mode, dashboard.execution_mode);
      const status = String(dashboard.overall_status || execution.overall_status || "unavailable");
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
          {!missingInputs.length && !attempted && status === "ready_for_execution" ? (
            <div className="rounded-lg border border-cyan-900/60 bg-cyan-950/20 p-4 text-sm text-cyan-100">
              Firmware co-simulation inputs are ready, but runtime execution was not requested for this run.
              {runtimeCapable ? " Re-run with firmware co-sim enabled to produce pass/fail results." : ""}
            </div>
          ) : null}
          <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
            <div className="space-y-3">
              {attempted ? (
                <>
                  <Bar label="Co-simulation passed" value={passed} total={executed} color="bg-emerald-500" />
                  <Bar label="Co-simulation failed" value={failed} total={executed} color="bg-rose-500" />
                </>
              ) : (
                <>
                  <Bar label="Planned tests" value={planned} total={Math.max(planned, 1)} color="bg-cyan-500" />
                  <Bar label="Executed tests" value={executed} total={Math.max(planned, 1)} color="bg-slate-500" />
                </>
              )}
            </div>
            <div className="grid grid-cols-2 gap-3">
              <Stat title="Status" value={status} />
              <Stat title="Planned" value={planned} />
              <Stat title="Executed" value={executed} />
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
              <Stat title="ELF" value={firmwareElfPlaceholder ? "placeholder" : String(dashboard.firmware_elf_detected ? "detected" : "missing")} />
              <Stat title="Runtime" value={attempted ? "attempted" : runtimeRequested ? "requested" : "not requested"} />
              {executionMode ? <Stat title="Mode" value={executionMode} /> : null}
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
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Package" value={String(pkg.package_status || "unavailable")} />
          </div>
        </div>
      );
    }

    if (stage === "product") {
      const model = record(evidence["system_product_capability_model.json"]);
      const pkg = record(evidence["system_product_package.json"]);
      const manifest = record(evidence["system_product_dashboard_manifest.json"]);
      const contract = record(evidence["system_product_collateral_contract.json"]);
      const packageArtifacts = record(pkg.artifacts);
      const lineage = record(model.lineage || contract.lineage);
      const sourceArtifacts = record(contract.source_artifacts);
      const firmwareSourceLoaded = Boolean(
        record(sourceArtifacts.firmware_dashboard).data ||
        record(sourceArtifacts.firmware_register_map).data ||
        record(sourceArtifacts.software_handoff).data
      );
      const capabilities = array(model.capabilities);
      const registers = array(model.registers);
      const specific = String(model.device_model || "generic_device_control") !== "generic_device_control";
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-5 lg:grid-cols-[1fr_320px]">
            <div>
              <div className="text-sm font-semibold text-slate-100">{String(model.product_name || "Product Dashboard")}</div>
              <div className="mt-2 text-sm text-slate-400">
                {String(record(model.product_experience).summary || "Generated simulator-backed product app.")}
              </div>
              {capabilities.length ? (
                <div className="mt-3 flex flex-wrap gap-2">
                  {capabilities.slice(0, 8).map((capability, index) => (
                    <span key={index} className="rounded border border-cyan-900/60 bg-cyan-950/20 px-3 py-2 text-xs text-cyan-200">
                      {String(record(capability).label || record(capability).id || "capability")}
                    </span>
                  ))}
                </div>
              ) : null}
            </div>
            <div className="grid grid-cols-2 gap-3">
              <Stat title="Model" value={String(model.device_model || "unavailable")} />
              <Stat title="Specific" value={specific ? "yes" : "generic"} />
              <Stat title="Capabilities" value={capabilities.length} />
              <Stat title="Registers" value={registers.length} />
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
              <Stat title="Runtime" value={String(pkg.runtime || lineage.target_runtime || "simulated_device")} />
            </div>
          </div>
          <div className="grid min-w-0 grid-cols-2 gap-3 md:grid-cols-4">
            <Stat title="Dashboard" value={String(manifest.entrypoint || pkg.entrypoint || packageArtifacts.dashboard || "not produced")} />
            <Stat title="Firmware Source" value={firmwareSourceLoaded ? "loaded" : "missing"} />
            <Stat title="Software Source" value={record(sourceArtifacts.software_api).data || record(sourceArtifacts.software_package).data ? "loaded" : "missing"} />
            <Stat title="Validation Source" value={record(sourceArtifacts.validation_summary).data ? "loaded" : "missing"} />
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
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
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
    const blocked = traceScenarios.length
      ? traceScenarios.filter((entry) => record(entry).trace_validation_status === "blocked").length
      : firstNumber(summary.scenario_blocked_count, execution.scenario_blocked_count);
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
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
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
  }, [agentCount, artifactsLoaded, evidence, error, resultsReady, stage, status, workflowId]);

  return (
    <section className="w-full rounded-lg border border-slate-800 bg-slate-950/45 p-5">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div>
          <div className="text-sm font-semibold text-white">Dashboard - Run Summary</div>
          <div className="mt-1 text-xs text-slate-400">Rendered from generated workflow artifacts.</div>
        </div>
        <div className="flex max-w-full flex-wrap items-center justify-end gap-2">
          {flow.map((item, index) => (
            <div key={item.id} className="flex items-center gap-2">
              <div className={`rounded px-2 py-1 text-xs ${index <= stageIndex ? "bg-cyan-500/20 text-cyan-200" : "bg-slate-800 text-slate-500"}`}>
                {item.label}
              </div>
              {index < flow.length - 1 ? <span className="text-slate-600">&gt;</span> : null}
            </div>
          ))}
        </div>
      </div>
      {content}
    </section>
  );
}
