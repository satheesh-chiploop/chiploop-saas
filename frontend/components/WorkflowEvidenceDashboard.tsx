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
  if (typeof value === "number" && Number.isFinite(value)) return value;
  if (typeof value === "string" && value.trim()) return value.trim();
  return "not produced";
}

function signedMetric(...values: unknown[]): string | number {
  const value = firstPresent(...values);
  if (typeof value === "number" && Number.isFinite(value)) return value;
  if (typeof value === "string" && value.trim()) return value.trim();
  return "not run";
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

function Stat({ title, value }: { title: string; value: string | number }) {
  return (
    <div className="min-w-0 rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="text-xs text-slate-400">{title}</div>
      <div className="mt-1 min-h-6 break-words text-base font-semibold leading-snug text-slate-100">{value}</div>
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

export default function WorkflowEvidenceDashboard({ workflowId, status, stage, logs }: Props) {
  const [evidence, setEvidence] = useState<Record<string, JsonMap | null>>({});
  const [error, setError] = useState<string | null>(null);
  const flow = useMemo(() => displayedFlow(stage), [stage]);
  const stageIndex = flow.findIndex((item) => item.id === stage);
  const agentCount = useMemo(() => countParticipatingAgents(logs), [logs]);

  useEffect(() => {
    if (!workflowId || status !== "completed") return;
    let active = true;
    const files: Record<Stage, string[]> = {
      arch2rtl: ["arch2rtl_dashboard.json", "digital_regmap.json", "upf_static_check.json"],
      dqa: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "rtl_lint_report.json",
        "cdc_findings.json",
        "reset_integrity_findings.json",
        "synthesis_readiness_findings.json",
        "executive_summary.json",
      ],
      smoke: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "simulation_manifest.json",
        "simulation_summary_coverage.json",
        "executive_summary.json",
      ],
      synthesis: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "implementation_setup_summary.json",
        "synth_summary.json",
        "metrics.json",
        "synthesis_metrics.json",
        "lec_summary.json",
        "upf_static_check.json",
        "scan_summary.json",
        "atpg_summary.json",
        "mbist_summary.json",
        "synthesis_readiness_findings.json",
        "executive_summary.json",
      ],
      tapeout: [
        "digital/handoff/rtl_handoff_ingest_manifest.json",
        "implementation_setup_summary.json",
        "synth_summary.json",
        "metrics.json",
        "synthesis_metrics.json",
        "lec_summary.json",
        "upf_static_check.json",
        "scan_summary.json",
        "atpg_summary.json",
        "mbist_summary.json",
        "floorplan_metrics.json",
        "floorplan_summary.json",
        "placement_metrics.json",
        "place_summary.json",
        "cts_summary.json",
        "route_metrics.json",
        "route_summary.json",
        "fill_summary.json",
        "drc_summary.json",
        "lvs_summary.json",
        "tapeout_package.json",
        "tapeout_summary.json",
        "tapeout_lec_summary.json",
        "executive_summary.json",
      ],
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
      product: [
        "system_product_dashboard_manifest.json",
        "system_product_package.json",
        "system_product_capability_model.json",
        "system_product_collateral_contract.json",
      ],
    };
    Promise.all((files[stage] || []).map(async (filename) => [filename.split("/").pop() || filename, await artifact(workflowId, filename)] as const))
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
      const dashboard = record(evidence["arch2rtl_dashboard.json"]);
      if (Object.keys(dashboard).length) {
        const lint = record(dashboard.lint);
        const storage = record(dashboard.storage);
        const timing = record(dashboard.timing);
        const iface = record(dashboard.interface);
        const clockReset = record(dashboard.clock_reset);
        const upf = record(evidence["upf_static_check.json"]);
        const hasUpf = Object.keys(upf).length > 0;
        const lintStatus = firstString(lint.status, "unavailable");
        return (
          <div className="mt-5 grid gap-5 2xl:grid-cols-[minmax(0,0.8fr)_minmax(0,1.2fr)]">
            <div className="space-y-3">
              <Bar label="Input bits" value={number(iface.input_count)} total={Math.max(number(iface.input_count) + number(iface.output_count), 1)} color="bg-cyan-500" />
              <Bar label="Output bits" value={number(iface.output_count)} total={Math.max(number(iface.input_count) + number(iface.output_count), 1)} color="bg-emerald-500" />
              <Bar label="Flip-flops" value={number(storage.flipflop_count)} total={Math.max(number(storage.flipflop_count) + number(storage.latch_count), 1)} color="bg-violet-500" />
              <Bar label="Latches" value={number(storage.latch_count)} total={Math.max(number(storage.flipflop_count) + number(storage.latch_count), 1)} color="bg-amber-500" />
            </div>
            <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 2xl:grid-cols-3">
              <Stat title="Lint" value={lintStatus} />
              <Stat title="Flip-flops" value={number(storage.flipflop_count)} />
              <Stat title="Latches" value={number(storage.latch_count)} />
              <Stat title="Full-cycle Paths" value={number(timing.full_cycle_path_count)} />
              <Stat title="Half-cycle Paths" value={number(timing.half_cycle_path_count)} />
              <Stat title="Input Bits" value={number(iface.input_count)} />
              <Stat title="Output Bits" value={number(iface.output_count)} />
              <Stat title="Input Ports" value={number(iface.input_port_count)} />
              <Stat title="Output Ports" value={number(iface.output_port_count)} />
              <Stat title="Clock" value={firstString(clockReset.primary_clock, "not inferred")} />
              <Stat title="Reset" value={firstString(clockReset.primary_reset, "not inferred")} />
              {hasUpf ? <Stat title="UPF Static" value={statusLabel(upf.status)} /> : null}
              {hasUpf ? <Stat title="Power Domains" value={metricValue(upf.domain_count)} /> : null}
              <Stat title="Modules" value={number(dashboard.module_count)} />
              <Stat title="RTL Files" value={number(dashboard.rtl_file_count)} />
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            </div>
          </div>
        );
      }
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

    if (stage === "dqa") {
      const handoff = record(evidence["rtl_handoff_ingest_manifest.json"]);
      const lint = record(evidence["rtl_lint_report.json"]);
      const cdc = record(evidence["cdc_findings.json"]);
      const reset = record(evidence["reset_integrity_findings.json"]);
      const readiness = record(evidence["synthesis_readiness_findings.json"]);
      const summary = record(evidence["executive_summary.json"]);
      const rtlFiles = firstNumber(
        handoff.rtl_file_count,
        array(handoff.rtl_files).length
      );
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-3 sm:grid-cols-1">
            <Bar label="RTL files imported" value={rtlFiles} total={Math.max(rtlFiles, 1)} color="bg-cyan-500" />
          </div>
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            <Stat title="Source" value={firstString(handoff.source_mode, "imported").replaceAll("_", " ")} />
            <Stat title="RTL Files" value={rtlFiles} />
            <Stat title="Top Module" value={firstString(handoff.top_module, "not inferred")} />
            <Stat title="Lint" value={lintVerdict(lint)} />
            <Stat title="CDC" value={findingsVerdict(cdc)} />
            <Stat title="Reset" value={findingsVerdict(reset)} />
            <Stat title="Synth Ready" value={synthesisReadinessVerdict(readiness)} />
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
      const setup = record(evidence["implementation_setup_summary.json"]);
      const synthSummary = record(evidence["synth_summary.json"]);
      const synth = record(evidence["metrics.json"] || evidence["synthesis_metrics.json"]);
      const lec = record(evidence["lec_summary.json"]);
      const upf = record(evidence["upf_static_check.json"]);
      const hasUpf = Object.keys(upf).length > 0;
      const dft = record(evidence["scan_summary.json"]);
      const atpg = record(evidence["atpg_summary.json"]);
      const mbist = record(evidence["mbist_summary.json"]);
      const floorplan = record(evidence["floorplan_summary.json"]);
      const place = record(evidence["place_summary.json"]);
      const cts = record(evidence["cts_summary.json"]);
      const route = record(evidence["route_summary.json"]);
      const fill = record(evidence["fill_summary.json"]);
      const drcSummary = record(evidence["drc_summary.json"]);
      const lvsSummary = record(evidence["lvs_summary.json"]);
      const tapeoutSummary = record(evidence["tapeout_summary.json"]);
      const tapeoutLec = record(evidence["tapeout_lec_summary.json"]);
      const summary = record(evidence["executive_summary.json"]);
      const staStages = record(summary.sta_stages);
      const postroute = record(staStages.sta_postroute);
      const postcts = record(staStages.sta_postcts);
      const postplace = record(staStages.sta_postplace);
      const preplace = record(staStages.sta_preplace);
      const wns = firstPresent(
        summary.worst_slack,
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
        postroute.tns,
        postcts.tns,
        postplace.tns,
        preplace.tns,
        synth.chiploop__sta_preplace_tns,
        synth.tns,
        synth.timing__setup__tns
      );
      const area = metricValue(summary.area, synth.area, synth.design__instance__area, synth.design__core__area);
      const cells = metricValue(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count);
      const flipflops = metricValue(synth.chiploop__flipflop_count, synth.flipflops, synth.ff_count, synth.registers, synth.design__instance__ff_count, synth["design__instance__count:flop"]);
      const latches = metricValue(synth.chiploop__latch_count, synth.latches, synth.latch_count, synth.design__instance__latch_count);
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
      const rtlFiles = firstNumber(handoff.rtl_file_count, array(handoff.rtl_files).length);
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
      const xor = metricValue(record(tapeoutSummary.signoff_inputs).xor_differences, tapeoutSummary.xor_differences, drcSummary.xor_differences, lvsSummary.xor_differences);
      const overall = stage === "tapeout" ? firstString(tapeoutSummary.status, summary.status, summary.verdict, status || "running") : firstString(summary.status, summary.verdict, synthSummary.status, status || "running");
      return (
        <div className="mt-5 space-y-5">
          <div className="grid gap-3 sm:grid-cols-2">
            <Bar label="RTL files imported" value={rtlFiles} total={Math.max(rtlFiles, 1)} color="bg-cyan-500" />
            <Bar label="Leaf cells" value={typeof cells === "number" ? cells : firstNumber(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count)} total={Math.max(firstNumber(summary.cell_count, synth.cells, synth.cell_count, synth.design__instance__count), 1)} color="bg-violet-500" />
          </div>
          <div className="grid min-w-0 grid-cols-1 gap-3 sm:grid-cols-2 xl:grid-cols-4">
            <Stat title="Source" value={firstString(handoff.source_mode, "imported").replaceAll("_", " ")} />
            <Stat title="Top Module" value={firstString(record(synthSummary.inputs).top_module, handoff.top_module, summary.design_name, "not inferred")} />
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
            <Stat title={stage === "tapeout" ? "Synthesis LEC Unproven" : "LEC Unproven"} value={metricValue(lec.unproven_points)} />
            {stage === "tapeout" ? <Stat title="Tapeout LEC" value={lecDashboardStatus(tapeoutLec)} /> : null}
            {stage === "tapeout" ? <Stat title="Tapeout LEC Unproven" value={metricValue(tapeoutLec.unproven_points)} /> : null}
            {hasUpf ? <Stat title="UPF Static" value={statusLabel(upf.status)} /> : null}
            {hasUpf ? <Stat title="Power Domains" value={metricValue(upf.domain_count)} /> : null}
            {hasUpf ? <Stat title="Isolation Rules" value={metricValue(upf.isolation_rule_count)} /> : null}
            {hasUpf ? <Stat title="Retention Rules" value={metricValue(upf.retention_rule_count)} /> : null}
            <Stat title="DFT" value={dftDashboardStatus(dft)} />
            <Stat title="Scan Chains" value={scanMetric(dft.status, firstPresent(dft.actual_scan_chains, dft.scan_chains))} />
            <Stat title="Scan Candidates" value={metricValue(dft.scan_flops)} />
            <Stat title="ATPG" value={atpgDashboardStatus(atpg)} />
            <Stat title="Patterns" value={atpgMetric(atpg.status, atpg.pattern_count)} />
            <Stat title="Stuck-at Coverage" value={atpgMetric(atpg.status, atpg.stuck_at_coverage_pct)} />
            <Stat title="MBIST" value={statusLabel(mbist.status)} />
            <Stat title="Memories" value={metricValue(mbist.memory_count)} />
            <Stat title="Memory Bits" value={metricValue(mbist.estimated_memory_bits)} />
            <Stat title="autombist" value={mbist.autombist_available === true ? "available" : mbist.autombist_available === false ? "not configured" : "not produced"} />
            {stage === "tapeout" ? <Stat title="Floorplan" value={statusLabel(floorplan.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Place" value={statusLabel(place.status)} /> : null}
            {stage === "tapeout" ? <Stat title="CTS" value={statusLabel(cts.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Route" value={statusLabel(route.status)} /> : null}
            {stage === "tapeout" ? <Stat title="Fill" value={statusLabel(fill.status)} /> : null}
            {stage === "tapeout" ? <Stat title="DRC Violations" value={drc} /> : null}
            {stage === "tapeout" ? <Stat title="LVS" value={lvs} /> : null}
            {stage === "tapeout" ? <Stat title="XOR Differences" value={xor} /> : null}
            {stage === "tapeout" ? <Stat title="Tapeout" value={statusLabel(tapeoutSummary.status)} /> : null}
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
            <Stat title="Summary" value={statusLabel(overall)} />
          </div>
        </div>
      );
    }

    if (stage === "verification") {
      const simulation = record(evidence["simulation_summary_coverage.json"]?.simulation);
      const coverage = record(evidence["simulation_summary_coverage.json"]?.coverage);
      const codeCoverage = record(coverage.code);
      const assertionCoverage = record(coverage.assertions);
      const formal = record(evidence["simulation_summary_coverage.json"]?.formal);
      const golden = record(evidence["simulation_summary_coverage.json"]?.golden_model);
      const toolchain = record(evidence["simulation_summary_coverage.json"]?.toolchain);
      const passed = number(simulation.pass);
      const failed = number(simulation.fail);
      const total = number(simulation.total);
      const codeStatus = String(codeCoverage.status || "");
      const formalStatus = String(formal.status || "not_enabled");
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
              {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
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
            {agentCount !== null ? <Stat title="Agents Participated" value={agentCount} /> : null}
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
  }, [agentCount, evidence, error, stage, status, workflowId]);

  return (
    <section className="rounded-lg border border-slate-800 bg-slate-950/45 p-5">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div>
          <div className="text-sm font-semibold text-white">Demo Evidence Dashboard</div>
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
