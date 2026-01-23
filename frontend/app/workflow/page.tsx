"use client";
// 10-15
import React, { useCallback, useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { getStableUserId } from "@/utils/userId"

import ReactFlow, {
  addEdge,
  Background,
  Controls,
  MiniMap,
  useEdgesState,
  useNodesState,
  Connection,
  Edge,
  Node,
  ReactFlowProvider,
  useReactFlow,
} from "reactflow";
import "reactflow/dist/style.css";
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
import AgentNode from "./AgentNode";
import WorkflowConsole from "./WorkflowConsole";
import PlannerModal from "@/components/PlannerModal";
import AgentPlannerModal from "@/components/AgentPlannerModal";
/* =========================
   Types & Constants
========================= */
type LoopKey = "digital" | "analog" | "embedded" | "system" |"validation";
type AgentNodeData = { uiLabel: string; backendLabel: string; desc?: string };

type CatalogItem = { uiLabel: string; backendLabel: string; desc?: string };

if (typeof window !== "undefined" && !localStorage.getItem("anon_user_id")) {
  localStorage.setItem("anon_user_id", crypto.randomUUID());
}

const LOOP_AGENTS: Record<LoopKey, CatalogItem[]> = {
  digital: [
    { uiLabel: "Digital Spec Agent", backendLabel: "Digital Spec Agent", desc: "Capture design spec & I/Os" },
    { uiLabel: "Digital RTL Agent", backendLabel: "Digital RTL Agent", desc: "Generate synthesizable RTL" },
    { uiLabel: "Digital Architecture Agent", backendLabel: "Digital Architecture Agent", desc: "Derives block-level architecture: interfaces, datapaths/control paths, and high-level tradeoffs from the digital spec" },
    { uiLabel: "Digital Microarchitecture Agent", backendLabel: "Digital Microarchitecture Agent", desc: "Refines architecture into implementable microarchitecture: FSMs, pipelines, queues, arbitration, and latency/throughput notes" },
    { uiLabel: "Digital Register Map Agent", backendLabel: "Digital Register Map Agent", desc: "Generates CSR/register map definitions: address map, fields, access types (RW/RO/WO), reset values, and side effects" },
    { uiLabel: "Digital Clock & Reset Architecture Agent", backendLabel: "Digital Clock & Reset Architecture AgentDigital Clock & Reset Architecture Agent", desc: "Defines clock/reset intent: clock domains, reset strategies, and CDC-aware intent (no implementation)" },
    { uiLabel: "Digital RTL Linting Agent", backendLabel: "Digital RTL Linting Agent", desc: "Runs RTL lint-style checks: coding guideline violations, synthesizability red flags, and style issues" },
    { uiLabel: "Digital CDC Analysis Agent", backendLabel: "Digital CDC Analysis Agent", desc: "Analyzes clock-domain crossings and flags required synchronizers/handshakes (intent-level, not tool-specific implementation)" },
    { uiLabel: "Digital Reset Integrity Agent", backendLabel: "Digital Reset Integrity Agent", desc: "Checks reset safety: async/sync usage patterns, deassertion concerns, reset-domain interactions, and common pitfalls" },
    { uiLabel: "Digital RTL Refactoring Agent", backendLabel: "Digital RTL Refactoring Agent", desc: "Improves RTL structure for readability/reuse: modularization suggestions and refactor patch scaffold (non-destructive)." },
    { uiLabel: "Digital Assertions (SVA) Agent", backendLabel: "Digital Assertions (SVA) Agent", desc: "Generates SystemVerilog Assertions (SVA) for protocols, safety checks, and basic liveness properties aligned to the spec/regmap" },
    { uiLabel: "Digital Testbench Generator Agent", backendLabel: "Digital Testbench Generator Agent", desc: "Generates Cocotb testbench skeletons (directed + constrained-random stub) and a Verilator-friendly Makefile using spec-derived clocks/resets/ports." },
    { uiLabel: "Digital Functional Coverage Agent", backendLabel: "Digital Functional Coverage Agent", desc: "Generates lightweight functional coverage sampling for Cocotb (optionally uses cocotb-coverage) and produces coverage reports." },
    { uiLabel: "Digital Golden Model Comparison Agent", backendLabel: "Digital Golden Model Comparison Agent", desc: "Generates a Python scoreboard + golden model stub for Cocotb; supports RTL vs reference model checks and scoreboarding" },
    { uiLabel: "Digital Simulation Control Agent", backendLabel: "Digital Simulation Control Agent", desc: "Generates regression orchestration (multi-test, multi-seed) for Cocotb+Verilator runs; seed management and JSON summary output" },
    { uiLabel: "Digital Bug Localization Agent", backendLabel: "Digital Bug Localization Agent", desc: "Heuristic failure root-cause hints by scanning logs for assertion/mismatch signatures; points to likely first divergence." },
    { uiLabel: "Digital Formal Verification Agent", backendLabel: "Digital Formal Verification Agent", desc: "Generates SymbiYosys orchestration configs and a minimal formal wrapper; optionally runs sby if available." },
    { uiLabel: "Digital Synthesis Readiness Agent", backendLabel: "Digital Synthesis Readiness Agent", desc: "Checks synthesizable subset red flags and runs open-source synthesis sanity (Yosys) to assess readiness; reports timing/area intent gaps from spec." },
    { uiLabel: "Digital Power Intent (UPF-lite) Agent", backendLabel: "Digital Power Intent (UPF-lite) Agent", desc: "Generates a UPF-lite power intent file (domains + optional isolation/retention) derived from spec/architecture (no hardcoding)." },
    { uiLabel: "Digital IP Packaging & Handoff Agent", backendLabel: "Digital IP Packaging & Handoff Agent", desc: "Creates SoC-ready IP package folder layout + manifest + checklist; bundles key RTL/docs/constraints/power/verification collateral." },
  ],
  analog: [
    { uiLabel: "Analog Spec Agent", backendLabel: "Analog Spec Agent", desc: "Analog specs & targets" },
    { uiLabel: "Analog Netlist Agent", backendLabel: "Analog Netlist Agent", desc: "Schematic/topology" },
    { uiLabel: "Analog Sim Agent", backendLabel: "Analog Sim Agent", desc: "SPICE/AMS runs" },
    { uiLabel: "Analog Result Agent", backendLabel: "Analog Result Agent", desc: "Summarize results" },
  ],
  embedded: [
    { uiLabel: "Embedded Spec Agent", backendLabel: "Embedded Spec Agent", desc: "Firmware/SoC reqs" },
    { uiLabel: "Embedded Code Agent", backendLabel: "Embedded Code Agent", desc: "Drivers & firmware" },
    { uiLabel: "Embedded Sim Agent", backendLabel: "Embedded Sim Agent", desc: "Run harness / co-sim" },
    { uiLabel: "Embedded Result Agent", backendLabel: "Embedded Result Agent", desc: "Summarize outputs" },
  ],
  validation:[
    { uiLabel: "Validation Instrument Setup Agent", backendLabel: "Validation Instrument Setup Agent", desc: "Resolves the user's bench setup from registered instruments (or defaults) and writes bench_setup.json for downstream validation agents." },
    { uiLabel: "Validation Test Plan Agent", backendLabel: "Validation Test Plan Agent", desc: "Generates a structured hardware validation test plan from datasheet/spec text; uses generic instrument types (psu/dmm/scope)." },
    { uiLabel: "Validation Scope Agent", backendLabel: "Validation Scope Agent", desc: "Applies user-selected scope (by tags or test names) to the generated validation test_plan and produces a scoped test plan for downstream sequence building." },
    { uiLabel: "Validation Sequence Builder Agent", backendLabel: "Validation Sequence Builder Agent", desc: "Builds an executable SCPI test sequence (steps) from bench_setup + test_plan (initially Keysight-class examples; transport is PyVISA/SCPI)." },
    { uiLabel: "Validation Execution Orchestrator Agent", backendLabel: "Validation Execution Orchestrator Agent", desc: "Executes the validation test_sequence and produces results artifacts. MVP uses a stub executor; next step swaps in real PyVISA I/O." },
    { uiLabel: "Validation Analytics Agent", backendLabel: "Validation Analytics Agent", desc: "Applies test_plan measurement limits (min/max) to captured results and generates analytics + a demo-ready report." },
    { uiLabel: "Validation Connectivity Intent Agent", backendLabel: "Validation Connectivity Intent Agent", desc: "Phase-1: Generates logical connectivity intent (bench template) from test plan. No physical resource strings; reusable across labs." },
    { uiLabel: "Validation Wiring Instructions Agent", backendLabel: "Validation Wiring Instructions Agent", desc: "Phase-1: Generates human-readable lab wiring instructions from connectivity intent (lab never logs into ChipLoop)." },
    { uiLabel: "Validation Preflight Agent", backendLabel: "Validation Preflight Agent", desc: "Phase-2a: Safe bench readiness checks (coverage + resource string sanity + optional *IDN?); no DUT stimulus. Supports stub or pyvisa mode." },
    { uiLabel: "Validation Bench Create Agent", backendLabel: "Validation Bench Create Agent", desc: "Creates a new validation bench and maps selected instruments to it. Outputs a creation report and summary." },
    { uiLabel: "Validation Test Plan Load Agent", backendLabel: "Validation Test Plan Load Agent", desc: "Loads a previously saved validation test plan from the database using test_plan_id and makes it available as state['test_plan'] for execution workflows (no datasheet/spec needed)." },
    { uiLabel: "Validation Bench Schematic Agent", backendLabel: "Validation Bench Schematic Agent", desc: "Generates bench_schematic.json (instruments + basic rail/probe templates) and persists it to validation_bench_connections.schematic for preflight/run mapping." },
    { uiLabel: "Validation Pattern Detection Agent", backendLabel: "Validation Pattern Detection Agent", desc: "Analyzes historical validation runs (facts + interpretations) for a given bench_id + test_plan_id and detects recurring clusters, flaky tests, and correlations. Writes patterns artifacts only; does not mutate WF4 execution artifacts." },
    { uiLabel: "Validation Apply Proposal Agent", backendLabel: "Validation Apply Proposal Agent", desc: "Applies a proposed test plan (from evolution or coverage proposal) by inserting vNext into validation_test_plans, deactivating previous active plan(s) for that user+name, and activating the new version. Deterministic; no LLM." },
    { uiLabel: "Validation Evolution Proposal Agent", backendLabel: "Validation Evolution Proposal Agent", desc: "WF7: Failure-driven diagnostic proposal. Hard no-op if no actionable failures found." },
    { uiLabel: "Validation Coverage Proposal Agent", backendLabel: "Validation Coverage Proposal Agent", desc: "WF8: Coverage intelligence + proposal. Computes gaps from recent run facts and proposes coverage tests." },
  ],
  system: [
    { uiLabel: "Digital Spec Agent", backendLabel: "Digital Spec Agent", desc: "System-level digital spec" },
    { uiLabel: "Digital RTL Agent", backendLabel: "Digital RTL Agent", desc: "Digital IP RTL design" },
    { uiLabel: "Digital Architecture Agent", backendLabel: "Digital Architecture Agent", desc: "Derives block-level architecture: interfaces, datapaths/control paths, and high-level tradeoffs from the digital spec" },
    { uiLabel: "Digital Microarchitecture Agent", backendLabel: "Digital Microarchitecture Agent", desc: "Refines architecture into implementable microarchitecture: FSMs, pipelines, queues, arbitration, and latency/throughput notes" },
    { uiLabel: "Digital Register Map Agent", backendLabel: "Digital Register Map Agent", desc: "Generates CSR/register map definitions: address map, fields, access types (RW/RO/WO), reset values, and side effects" },
    { uiLabel: "Digital Clock & Reset Architecture Agent", backendLabel: "Digital Clock & Reset Architecture AgentDigital Clock & Reset Architecture Agent", desc: "Defines clock/reset intent: clock domains, reset strategies, and CDC-aware intent (no implementation)" },
    { uiLabel: "Digital RTL Linting Agent", backendLabel: "Digital RTL Linting Agent", desc: "Runs RTL lint-style checks: coding guideline violations, synthesizability red flags, and style issues" },
    { uiLabel: "Digital CDC Analysis Agent", backendLabel: "Digital CDC Analysis Agent", desc: "Analyzes clock-domain crossings and flags required synchronizers/handshakes (intent-level, not tool-specific implementation)" },
    { uiLabel: "Digital Reset Integrity Agent", backendLabel: "Digital Reset Integrity Agent", desc: "Checks reset safety: async/sync usage patterns, deassertion concerns, reset-domain interactions, and common pitfalls" },
    { uiLabel: "Digital RTL Refactoring Agent", backendLabel: "Digital RTL Refactoring Agent", desc: "Improves RTL structure for readability/reuse: modularization suggestions and refactor patch scaffold (non-destructive)." },
    { uiLabel: "Digital Assertions (SVA) Agent", backendLabel: "Digital Assertions (SVA) Agent", desc: "Generates SystemVerilog Assertions (SVA) for protocols, safety checks, and basic liveness properties aligned to the spec/regmap" },
    { uiLabel: "Digital Testbench Generator Agent", backendLabel: "Digital Testbench Generator Agent", desc: "Generates Cocotb testbench skeletons (directed + constrained-random stub) and a Verilator-friendly Makefile using spec-derived clocks/resets/ports." },
    { uiLabel: "Digital Functional Coverage Agent", backendLabel: "Digital Functional Coverage Agent", desc: "Generates lightweight functional coverage sampling for Cocotb (optionally uses cocotb-coverage) and produces coverage reports." },
    { uiLabel: "Digital Golden Model Comparison Agent", backendLabel: "Digital Golden Model Comparison Agent", desc: "Generates a Python scoreboard + golden model stub for Cocotb; supports RTL vs reference model checks and scoreboarding" },
    { uiLabel: "Digital Simulation Control Agent", backendLabel: "Digital Simulation Control Agent", desc: "Generates regression orchestration (multi-test, multi-seed) for Cocotb+Verilator runs; seed management and JSON summary output" },
    { uiLabel: "Digital Bug Localization Agent", backendLabel: "Digital Bug Localization Agent", desc: "Heuristic failure root-cause hints by scanning logs for assertion/mismatch signatures; points to likely first divergence." },
    { uiLabel: "Digital Formal Verification Agent", backendLabel: "Digital Formal Verification Agent", desc: "Generates SymbiYosys orchestration configs and a minimal formal wrapper; optionally runs sby if available." },
    { uiLabel: "Digital Synthesis Readiness Agent", backendLabel: "Digital Synthesis Readiness Agent", desc: "Checks synthesizable subset red flags and runs open-source synthesis sanity (Yosys) to assess readiness; reports timing/area intent gaps from spec." },
    { uiLabel: "Digital Power Intent (UPF-lite) Agent", backendLabel: "Digital Power Intent (UPF-lite) Agent", desc: "Generates a UPF-lite power intent file (domains + optional isolation/retention) derived from spec/architecture (no hardcoding)." },
    { uiLabel: "Digital IP Packaging & Handoff Agent", backendLabel: "Digital IP Packaging & Handoff Agent", desc: "Creates SoC-ready IP package folder layout + manifest + checklist; bundles key RTL/docs/constraints/power/verification collateral." },
    { uiLabel: "Validation Instrument Setup Agent", backendLabel: "Validation Instrument Setup Agent", desc: "Resolves the user's bench setup from registered instruments (or defaults) and writes bench_setup.json for downstream validation agents." },
    { uiLabel: "Validation Test Plan Agent", backendLabel: "Validation Test Plan Agent", desc: "Generates a structured hardware validation test plan from datasheet/spec text; uses generic instrument types (psu/dmm/scope)." },
    { uiLabel: "Validation Scope Agent", backendLabel: "Validation Scope Agent", desc: "Applies user-selected scope (by tags or test names) to the generated validation test_plan and produces a scoped test plan for downstream sequence building." },
    { uiLabel: "Validation Sequence Builder Agent", backendLabel: "Validation Sequence Builder Agent", desc: "Builds an executable SCPI test sequence (steps) from bench_setup + test_plan (initially Keysight-class examples; transport is PyVISA/SCPI)." },
    { uiLabel: "Validation Execution Orchestrator Agent", backendLabel: "Validation Execution Orchestrator Agent", desc: "Executes the validation test_sequence and produces results artifacts. MVP uses a stub executor; next step swaps in real PyVISA I/O." },
    { uiLabel: "Validation Analytics Agent", backendLabel: "Validation Analytics Agent", desc: "Applies test_plan measurement limits (min/max) to captured results and generates analytics + a demo-ready report." },
    { uiLabel: "Validation Connectivity Intent Agent", backendLabel: "Validation Connectivity Intent Agent", desc: "Phase-1: Generates logical connectivity intent (bench template) from test plan. No physical resource strings; reusable across labs." },
    { uiLabel: "Validation Wiring Instructions Agent", backendLabel: "Validation Wiring Instructions Agent", desc: "Phase-1: Generates human-readable lab wiring instructions from connectivity intent (lab never logs into ChipLoop)." },
    { uiLabel: "Validation Preflight Agent", backendLabel: "Validation Preflight Agent", desc: "Phase-2a: Safe bench readiness checks (coverage + resource string sanity + optional *IDN?); no DUT stimulus. Supports stub or pyvisa mode." },
    { uiLabel: "Validation Bench Create Agent", backendLabel: "Validation Bench Create Agent", desc: "Creates a new validation bench and maps selected instruments to it. Outputs a creation report and summary." },
    { uiLabel: "Validation Test Plan Load Agent", backendLabel: "Validation Test Plan Load Agent", desc: "Loads a previously saved validation test plan from the database using test_plan_id and makes it available as state['test_plan'] for execution workflows (no datasheet/spec needed)." },
    { uiLabel: "Validation Bench Schematic Agent", backendLabel: "Validation Bench Schematic Agent", desc: "Generates bench_schematic.json (instruments + basic rail/probe templates) and persists it to validation_bench_connections.schematic for preflight/run mapping." },
    { uiLabel: "Validation Bench Schematic Load + Mapping Agent", backendLabel: "Validation Bench Schematic Load + Mapping Agent", desc: "Loads bench schematic from validation_bench_connections and reconciles with bench_setup to generate execution_mapping.json for WF4." },
    { uiLabel: "Validation Pattern Detection Agent", backendLabel: "Validation Pattern Detection Agent", desc: "Analyzes historical validation runs (facts + interpretations) for a given bench_id + test_plan_id and detects recurring clusters, flaky tests, and correlations. Writes patterns artifacts only; does not mutate WF4 execution artifacts." },
    { uiLabel: "Validation Apply Proposal Agent", backendLabel: "Validation Apply Proposal Agent", desc: "Applies a proposed test plan (from evolution or coverage proposal) by inserting vNext into validation_test_plans, deactivating previous active plan(s) for that user+name, and activating the new version. Deterministic; no LLM." },
    { uiLabel: "Validation Evolution Proposal Agent", backendLabel: "Validation Evolution Proposal Agent", desc: "WF7: Failure-driven diagnostic proposal. Hard no-op if no actionable failures found." },
    { uiLabel: "Validation Coverage Proposal Agent", backendLabel: "Validation Coverage Proposal Agent", desc: "WF8: Coverage intelligence + proposal. Computes gaps from recent run facts and proposes coverage tests." },
    { uiLabel: "Embedded Code Agent", backendLabel: "Embedded Code Agent", desc: "Embedded driver / firmware" },
    { uiLabel: "Embedded Spec Agent", backendLabel: "Embedded Spec Agent", desc: "Firmware simulation harness" },
    { uiLabel: "Embedded Sim Agent", backendLabel: "Embedded Sim Agent", desc: "Run harness / co-sim" },
    { uiLabel: "Embedded Result Agent", backendLabel: "Embedded Result Agent", desc: "Summarize hardware + firmware integration" },
    { uiLabel: "System CoSim Integration Agent", backendLabel: "System CoSim Integration Agent", desc: "Generates co-sim scaffolding: AXI4-Lite register block template + firmware MMIO header + basic cocotb smoke test" },
    { uiLabel: "System ISS Bridge Agent", backendLabel: "System ISS Bridge Agent", desc: "Generates scaffolding for an ISS<->RTL bridge (MMIO/IRQ contract + Verilator harness skeleton + run notes)" },
  ],
};
//const [showPlanner, setShowPlanner] = useState(false);

//{showPlanner && <PlannerModal onClose={() => setShowPlanner(false)} />}

function computeMissingInstrumentTypes(plan: any, selectedNames: string[], selectedInstrumentRows: any[]) {
  const selectedSet = new Set(selectedNames);

  const needed = new Set<string>();
  for (const t of (plan?.tests || [])) {
    if (!t?.name) continue;
    if (!selectedSet.has(t.name)) continue;
    for (const it of (t.required_instruments || [])) needed.add(String(it));
  }

  const have = new Set<string>();
  for (const inst of (selectedInstrumentRows || [])) {
    if (inst?.instrument_type) have.add(String(inst.instrument_type));
  }

  const missing: string[] = [];
  for (const req of needed) if (!have.has(req)) missing.push(req);

  return missing;
}





/* =========================
   Page Wrapper
========================= */
export default function WorkflowPageWrapper() {
  return (
    <ReactFlowProvider>
      <WorkflowPage />
    </ReactFlowProvider>
  );
}

/* =========================
   Main Page
========================= */
function WorkflowPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const rf = useReactFlow();

  // core state
  const [loop, setLoop] = useState<LoopKey>("digital");
  const [nodes, setNodes, onNodesChange] = useNodesState<Node<AgentNodeData>>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [jobId, setJobId] = useState<string | null>(null);

  // local catalog states
  const [customAgents, setCustomAgents] = useState<CatalogItem[]>([]);

  type CustomWorkflowRow = { name: string; loop_type?: string | null };
  const [customWorkflows, setCustomWorkflows] = useState<CustomWorkflowRow[]>([]);



  const [loadingAgents, setLoadingAgents] = useState(true);
  const [loadingWorkflows, setLoadingWorkflows] = useState(true);
  const [designIntents, setDesignIntents] = useState<any[]>([]);
  
  // modals
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);
  const [showPlanner, setShowPlanner] = useState(false);
  const [showAgentPlanner, setShowAgentPlanner] = useState(false);
  const [selectedWorkflowName, setSelectedWorkflowName] = useState<string | null>(null);
  const {fitView} = useReactFlow();

  const [contextMenu, setContextMenu] = useState<{x:number; y:number; name:string} | null>(null);
  const [renameTarget, setRenameTarget] = useState<{oldName:string, newName:string}>({oldName:"", newName:""});

  // Validation instrument picker (only used when loop === "validation")

  const [instrumentLoadErr, setInstrumentLoadErr] = useState<string | null>(null);

  const [showInstrumentPicker, setShowInstrumentPicker] = useState(false);
  const [validationInstruments, setValidationInstruments] = useState<any[]>([]);
  const [selectedInstrumentIds, setSelectedInstrumentIds] = useState<string[]>([]);

  const [pendingSpecText, setPendingSpecText] = useState<string>("");
  const [pendingSpecFile, setPendingSpecFile] = useState<File | undefined>(undefined);
  const [pendingWorkflowPayload, setPendingWorkflowPayload] = useState<any>(null);
  const [pendingValidationRun, setPendingValidationRun] = useState(false);

  const [showScopeModal, setShowScopeModal] = useState(false);
  const [previewTestPlan, setPreviewTestPlan] = useState<any>(null);
  const [selectedTestNames, setSelectedTestNames] = useState<string[]>([]);
  const [missingInstrumentTypes, setMissingInstrumentTypes] = useState<string[]>([]);

  const [selectedInstrumentRows, setSelectedInstrumentRows] = useState<any[]>([]);

  const [selectedWorkflowId, setSelectedWorkflowId] = useState<string | null>(null);
  const [selectedWorkflowLoopType, setSelectedWorkflowLoopType] = useState<string | null>(null);

  const [showBenchPicker, setShowBenchPicker] = useState(false);
  const [validationBenches, setValidationBenches] = useState<any[]>([]);
  const [selectedBenchId, setSelectedBenchId] = useState<string>("");

    // ✅ Bench schematic viewer (bench picker)

 
  const [benchSchematicError, setBenchSchematicError] = useState<string | null>(null);
  const [benchSchematicRow, setBenchSchematicRow] = useState<any | null>(null);
  const [benchSchematicLoading, setBenchSchematicLoading] = useState(false);

  const [benchName, setBenchName] = useState("");
  const [benchLocation, setBenchLocation] = useState("");

  const [testPlanName, setTestPlanName] = useState("");

  const [showBenchSchematicModal, setShowBenchSchematicModal] = useState(false);
  const [benchSchematicObj, setBenchSchematicObj] = useState<any | null>(null);
  const [benchSchematicErr, setBenchSchematicErr] = useState<string | null>(null);
  const [benchSchematicModalLoading, setBenchSchematicModalLoading] = useState(false);

  const inferLoopTypeFromName = (name: string): string => {
    if (!name) return "digital";
    if (name.startsWith("Validation_")) return "validation";
    if (name.startsWith("System_")) return "system";
    if (name.startsWith("Analog_")) return "analog";
    if (name.startsWith("Embedded_")) return "embedded";
    return "digital"; // default
  };
  

  const openBenchSchematic = async (benchId: string) => {
    setBenchSchematicErr(null);
    setBenchSchematicObj(null);
    setBenchSchematicModalLoading(true);
    setShowBenchSchematicModal(true);

    try {
      const { data, error } = await supabase
        .from("validation_bench_connections")
        .select("schematic")
        .eq("bench_id", benchId)
        .limit(1)
        .single();

      if (error) throw error;

      // table holds { schematic: {...} } or could be empty
      const schematic = data?.schematic || {};
      setBenchSchematicObj(schematic);
    } catch (e: any) {
      setBenchSchematicErr(e?.message || "Failed to load bench schematic");
    } finally {
      setBenchSchematicModalLoading(false);
    }
  };






  // lightweight "add instrument" form inside the modal
  const [newInstrument, setNewInstrument] = useState({
    nickname: "",
    vendor: "Keysight",
    model: "",
    instrument_type: "psu",      // psu | dmm | scope
    transport: "pyvisa",         // keep as "pyvisa"
    interface: "TCPIP",          // TCPIP | USB | GPIB
    resource_string: "",
  });
  
  const openContextMenu = (e: React.MouseEvent, name: string) => {
    e.preventDefault();
    setContextMenu({ x: e.clientX, y: e.clientY, name });
  };
  
  const closeContextMenu = () => setContextMenu(null);

  type RunRecord = {
    run_id: string;        // workflow_id returned by backend
    run_name: string;      // friendly name (Save-as prompt)
    created_at: string;    // ISO
  };
  
  const runStorageKey = (workflowName: string) => `workflow_runs__${workflowName}`;
  
  const loadRunsForWorkflow = (workflowName: string): RunRecord[] => {
    if (typeof window === "undefined") return [];
    try {
      const raw = localStorage.getItem(runStorageKey(workflowName));
      if (!raw) return [];
      const parsed = JSON.parse(raw);
      if (!Array.isArray(parsed)) return [];
      return parsed;
    } catch {
      return [];
    }
  };
  
  const saveRunsForWorkflow = (workflowName: string, runs: RunRecord[]) => {
    if (typeof window === "undefined") return;
    localStorage.setItem(runStorageKey(workflowName), JSON.stringify(runs));
  };
  
  const defaultRunName = (workflowName: string) => {
    const d = new Date();
    const yyyyMmDd = d.toISOString().slice(0, 10);
    const hh = String(d.getHours()).padStart(2, "0");
    const mm = String(d.getMinutes()).padStart(2, "0");
    return `${workflowName}_${yyyyMmDd}_${hh}${mm}`;
  };

  const [runs, setRuns] = useState<RunRecord[]>([]);
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null);
  const [pendingRunName, setPendingRunName] = useState<string | null>(null);

  
  
  const deleteCustomWorkflow = async (name: string) => {
    try {
      const userId = await getStableUserId(supabase);  // ✅ unified ID

      const res = await fetch(`${API_BASE}/delete_custom_workflow?name=${encodeURIComponent(name)}&user_id=${userId}`, {
        method: "DELETE"
      });

      const j = await res.json();
      if (j.status !== "ok") {
        alert("Delete failed");
        return;
      }

      await loadCustomWorkflowsFromDB();  // ✅ refresh sidebar list
      if (name === selectedWorkflowName) {
        setSelectedWorkflowName(null);
      }
    } catch (err) {
      console.error("Delete failed", err);
      alert("❌ Could not delete workflow.");
    } finally {
      closeContextMenu();
    }
  };
  
  const renameCustomWorkflow = async () => {
    try {
      if (!renameTarget.newName.trim()) {
        alert("Enter a valid new name.");
        return;
      }
      // local optimistic update
      const oldKey = `workflow_${renameTarget.oldName}`;
      const newKey = `workflow_${renameTarget.newName}`;
  
      const cached = localStorage.getItem(oldKey);
      if (cached) {
        localStorage.removeItem(oldKey);
        localStorage.setItem(newKey, cached);
      }

      setCustomWorkflows((prev) =>
        prev.map((w) =>
          w.name === renameTarget.oldName
            ? { ...w, name: renameTarget.newName }
            : w
        )
      );
      
      // setCustomWorkflows((prev) =>
      //  prev.map((n) => (n === renameTarget.oldName ? renameTarget.newName : n))
      //);
  
      // backend rename
      const res = await fetch(`${API_BASE}/rename_custom_workflow`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(renameTarget),
      });
      const j = await res.json();
      if (j.status !== "ok") {
        alert(`⚠️ Rename failed: ${j.message || "Unknown error"}`);
        await loadCustomWorkflowsFromDB();
        return;
      }
  
      await loadCustomWorkflowsFromDB();
    } catch (err) {
      console.error("Rename failed", err);
      alert("❌ Could not rename workflow.");
    } finally {
      setRenameTarget({ oldName: "", newName: "" });
      closeContextMenu();
    }
  };
  const publishCustomWorkflow = async (name: string) => {
    try {
      const userId = await getStableUserId(supabase);  // ✅ unified ID

      const res = await fetch(`${API_BASE}/publish_custom_workflow`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          workflow_name: name,
          user_id: userId,
        }),
      });

      const j = await res.json();
      if (j.status !== "ok") {
        alert(`⚠️ Publish failed: ${j.message || "Unknown error"}`);
        return;
      }

      alert("✅ Workflow submitted to marketplace for review.");
    } catch (err) {
      console.error("Publish custom workflow failed", err);
      alert("❌ Could not publish workflow.");
    } finally {
      closeContextMenu();
    }
  };

  const openDesignIntentJsonEditor = (intent: any) => {
    console.log("🧾 Edit Design Intent via JSON editor:", intent?.id, intent?.title);
  
    // 1️⃣ Ensure the planner modal is visible
    setShowPlanner(true);
  
    // 2️⃣ After the modal mounts and attaches the listener, fire the event
    setTimeout(() => {
      window.dispatchEvent(
        new CustomEvent("openJsonEditorForDesignIntent", {
          detail: intent,
        })
      );
    }, 0);
  };
  const fetchValidationInstruments = async () => {
    setInstrumentLoadErr(null);
    try {
      const userId = await getStableUserId(supabase);

      const res = await fetch(`${API_BASE}/validation/instruments`, {
        headers: { "x-user-id": userId },
      });
      const j = await res.json();
      if (!res.ok || !j.ok) throw new Error(j.detail || "Failed to load instruments");

      const items = j.instruments || [];
      setValidationInstruments(items);

      const defaults = items.filter((x: any) => x.is_default).map((x: any) => x.id);
      if (defaults.length > 0) setSelectedInstrumentIds(defaults);

    } catch (e: any) {
      setInstrumentLoadErr(e.message || "Failed to load instruments");
    }
  };
  
  const registerValidationInstrument = async () => {
    try {
      const userId = await getStableUserId(supabase);

      const res = await fetch(`${API_BASE}/validation/instruments/register`, {
        method: "POST",
        headers: { "Content-Type": "application/json", "x-user-id": userId },
        body: JSON.stringify({ ...newInstrument }),
      });
      const j = await res.json();
      if (!res.ok || !j.ok) throw new Error(j.detail || "Register failed");

      await fetchValidationInstruments();

      if (j.instrument?.id) {
        setSelectedInstrumentIds((prev) => Array.from(new Set([...prev, j.instrument.id])));

        await fetch(`${API_BASE}/validation/instruments/${j.instrument.id}/probe`, {
          method: "POST",
          headers: { "x-user-id": userId },
        });
      }
      
      setNewInstrument((s) => ({ ...s, nickname: "", model: "", resource_string: "" }));
    } catch (e: any) {
      alert(e.message || "Register failed");
    }
  };
  
  const toggleInstrument = (id: string) => {
    setSelectedInstrumentIds((prev) =>
      prev.includes(id) ? prev.filter((x) => x !== id) : [...prev, id]
    );
  };
 
  
  
  // NEW: agent context menu state
  const [agentMenu, setAgentMenu] = useState<{ x: number; y: number; name: string } | null>(null);

    // 🌿 Design Intent context menu
  const [designIntentMenu, setDesignIntentMenu] = useState<{
      x: number;
      y: number;
      intent: any;
  } | null>(null);
  
  const openDesignIntentMenu = (e: React.MouseEvent, intent: any) => {
      e.preventDefault();
      setDesignIntentMenu({ x: e.clientX, y: e.clientY, intent });
  };
  
  const closeDesignIntentMenu = () => setDesignIntentMenu(null);
  

  const openAgentMenu = (e: React.MouseEvent, name: string) => {
    e.preventDefault();
    setAgentMenu({ x: e.clientX, y: e.clientY, name });
  };
  const closeAgentMenu = () => setAgentMenu(null);

// NEW: API calls
  const renameCustomAgent = async (oldName: string) => {
    const newName = prompt("New agent name:", oldName) || "";
    if (!newName || newName === oldName) return;
    const res = await fetch(`${API_BASE}/rename_custom_agent`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ old_name: oldName, new_name: newName }),
    });
    const j = await res.json();
    if (j.status !== "ok") {
      alert(`⚠️ Rename failed: ${j.message || "Unknown error"}`);
    } else {
      window.dispatchEvent(new Event("refreshAgents")); // reuse your existing refresh pattern
    }
    closeAgentMenu();
  };

  const deleteCustomAgent = async (name: string) => {
    const userId = await getStableUserId(supabase);  // ✅ unify ID

    const res = await fetch(`${API_BASE}/delete_custom_agent?name=${encodeURIComponent(name)}&user_id=${userId}`, {
      method: "DELETE"
    });

    const j = await res.json();
    if (j.status !== "ok") {
      alert(`Delete failed: ${j.message}`);
      return;
    }

    window.dispatchEvent(new Event("refreshAgents"));
    window.dispatchEvent(new Event("refreshWorkflows"));
    closeAgentMenu();
  };
  const publishCustomAgent = async (name: string) => {
    try {
      const userId = await getStableUserId(supabase);  // ✅ unified ID

      const res = await fetch(`${API_BASE}/publish_custom_agent`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          agent_name: name,
          user_id: userId,
        }),
      });

      const j = await res.json();
      if (j.status !== "ok") {
        alert(`⚠️ Publish failed: ${j.message || "Unknown error"}`);
        return;
      }

      alert("✅ Agent submitted to marketplace for review.");
    } catch (err) {
      console.error("Publish custom agent failed", err);
      alert("❌ Could not publish agent.");
    } finally {
      closeAgentMenu();
    }
  };


  const renameDesignIntent = async (intent: any) => {
    try {
      const currentTitle = intent.title || "Untitled Design Intent";
      const newTitle = prompt("New name for this Design Intent:", currentTitle) || "";
      if (!newTitle.trim() || newTitle === currentTitle) {
        closeDesignIntentMenu();
        return;
      }

      const { error } = await supabase
        .from("design_intent_drafts")
        .update({ title: newTitle })
        .eq("id", intent.id);

      if (error) {
        console.error("❌ Rename design intent failed:", error.message);
        alert("Rename failed. Please try again.");
      } else {
        await loadIntents(); // refresh sidebar list
      }
    } catch (err) {
      console.error("❌ Rename design intent error:", err);
    } finally {
      closeDesignIntentMenu();
    }
  };

  type ValidationTestPlan = {
    id: string;
    name: string;
    description?: string | null;
    created_at?: string | null;
  };
  
  const [validationTestPlans, setValidationTestPlans] = useState<ValidationTestPlan[]>([]);
  const [selectedTestPlanId, setSelectedTestPlanId] = useState<string>("");
  const fetchValidationTestPlans = async () => {
    try {
      const userId = await getStableUserId(supabase);
  
      const resp = await fetch(`${API_BASE}/validation/test_plans?user_id=${userId}`);
      const json = await resp.json();
  
      if (json?.status === "ok") {
        setValidationTestPlans(json.plans || []);
      } else {
        console.warn("[validation test plans] unexpected:", json);
        setValidationTestPlans([]);
      }
    } catch (e) {
      console.error("[validation test plans] fetch failed:", e);
      setValidationTestPlans([]);
    }
  };
    

  const loadBenches = async () => {
    const { data, error } = await supabase
      .from("validation_benches")
      .select("id,name,location,status")
      .order("created_at", { ascending: false });
  
    if (!error) setValidationBenches(data || []);
  };

  const loadBenchSchematic = async (benchId: string) => {
    setBenchSchematicLoading(true);
    setBenchSchematicError(null);
    setBenchSchematicRow(null);

    try {
      const { data, error } = await supabase
        .from("validation_bench_connections")
        .select("id, bench_id, schematic, updated_at")
        .eq("bench_id", benchId)
        .order("updated_at", { ascending: false })
        .limit(1);

      if (error) throw error;

      if (!data || data.length === 0) {
        setBenchSchematicError("No schematic found for this bench. Run WF2 'Create Bench' + 'Schematic Agent' first.");
      } else {
        setBenchSchematicRow(data[0]);
      }
    } catch (e: any) {
      console.error("❌ loadBenchSchematic failed:", e);
      setBenchSchematicError(e?.message || "Failed to load bench schematic");
    } finally {
      setBenchSchematicLoading(false);
    }
  };

  

  const deleteDesignIntent = async (intent: any) => {
    try {
      if (!confirm(`Delete design intent "${intent.title || "Untitled"}"?`)) {
        closeDesignIntentMenu();
        return;
      }

      const { error } = await supabase
        .from("design_intent_drafts")
        .delete()
        .eq("id", intent.id);

      if (error) {
        console.error("❌ Delete design intent failed:", error.message);
        alert("Delete failed. Please try again.");
      } else {
        await loadIntents(); // refresh sidebar list
      }
    } catch (err) {
      console.error("❌ Delete design intent error:", err);
    } finally {
      closeDesignIntentMenu();
    }
  };


  // 🔁 Ensure sidebar visible once agents/workflows are loaded
  useEffect(() => {
    if (customAgents.length > 0 || customWorkflows.length > 0) {
      setLoadingAgents(false);
      setLoadingWorkflows(false);
    }
  }, [customAgents, customWorkflows]);

  // Load Saved Design Intents
  const loadIntents = async () => {
    const stableId = await getStableUserId(supabase);
    const { data } = await supabase
      .from("design_intent_drafts")
      .select("*")
      .eq("user_id", stableId)
      .order("created_at", { ascending: false });

    setDesignIntents(data || []);
  };

  const loadDesignIntent = (item: any) => {
    window.dispatchEvent(
      new CustomEvent("loadDesignIntent", { detail: item })
    );
    setShowPlanner(true); // Opens Planner with loaded data
  };

  useEffect(() => {
    const handler = () => loadIntents();
    window.addEventListener("refreshDesignIntents", handler);
    return () => window.removeEventListener("refreshDesignIntents", handler);
  }, []);

  const anonUserId =
    typeof window !== "undefined"
      ? localStorage.getItem("anon_user_id")
      : "anonymous";
  
  useEffect(() => {
    if (nodes.length > 0 || edges.length > 0) {
      fitView({ padding: 0.15, duration: 500 });
    }
  }, [nodes, edges, fitView]);
  
  // workflow console tab state
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "output">("summary");

  /* ---------- Auth gate ---------- */
  useEffect(() => {
    (async () => {
      setLoadingAgents(true);
      setLoadingWorkflows(true);
  
      const { data: { session } } = await supabase.auth.getSession();
      if (!session) {
        router.push("/login");
        return;
      }
  
      try {
        
        const savedWF = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
        // ✅ Load custom agents per user from Supabase
        const { data: { session } } = await supabase.auth.getSession();
        const userId = session?.user?.id || localStorage.getItem("anon_user_id") || "anonymous";

        const { data } = await supabase
          .from("agents")
          .select("*")
          .eq("owner_id", userId)
          .order("created_at", { ascending: false });

        await loadIntents()

        setCustomAgents(
            (data || []).map(a => ({
              uiLabel: a.agent_name,
              backendLabel: a.agent_name,
              desc: a.description || "",
            }))
        );

        setCustomWorkflows(
          savedWF.map((k) => {
            const name = k.replace("workflow_", "");
            return { name, loop_type: inferLoopTypeFromName(name) };
          })
        );
        
        // setCustomWorkflows(savedWF.map((k) => k.replace("workflow_", "")));
  
        // Load from Supabase after local cache
        setTimeout(() => loadCustomWorkflowsFromDB(), 600);
      } catch (err) {
        console.error("❌ Error loading user or workflows:", err);
      } finally {
        setLoadingAgents(false);
        setLoadingWorkflows(false);
      }
    })();
  }, [supabase, router]);

  // 🔁 Listen for new workflows saved by PlannerModal
  // 🔁 Listen for global refresh events (Planner or Save)
  useEffect(() => {
    const refreshHandler = () => {
      console.log("🔄 Refreshing workflows (global trigger)");
      loadCustomWorkflowsFromDB();
    };
    window.addEventListener("refreshWorkflows", refreshHandler);
    return () => window.removeEventListener("refreshWorkflows", refreshHandler);
  }, []);

  useEffect(() => {
    const handler = (e: any) => {
      const graph = e.detail;
      if (!graph) return;
  
      console.log("🎯 Received workflow graph from System Planner:", graph);
  
      // Normalize nodes to match ReactFlow agentNode structure
      const newNodes = (graph.nodes || []).map((n: any, idx: number) => ({
        id: n.id || `n${idx}`,
        type: "agentNode",
        position: n.position || { x: 120 * idx, y: 200 },
        data: {
          uiLabel: n.data?.uiLabel || n.data?.backendLabel || n.label || "Agent",
          backendLabel: n.data?.backendLabel || n.data?.uiLabel || n.label || "Unknown Agent",
          desc: n.data?.desc || "",
        },
      }));
  
      const newEdges = (graph.edges || []).map((e: any, idx: number) => ({
        id: e.id || `e${idx}`,
        source: e.source,
        target: e.target,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      }));
  
      setNodes(newNodes);
      setEdges(newEdges);
  
      setTimeout(() => fitView({ padding: 0.25 }), 50);
    };
  
    window.addEventListener("loadWorkflowGraph", handler);
    return () => window.removeEventListener("loadWorkflowGraph", handler);
  }, [setNodes, setEdges, fitView]);  

  useEffect(() => {
    const refreshAgents = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const userId = session?.user?.id || localStorage.getItem("anon_user_id") || "anonymous";
  
      const { data } = await supabase
        .from("agents")
        .select("*")
        .eq("owner_id", userId)
        .order("created_at", { ascending: false });
  
      setCustomAgents(
        (data || []).map(a => ({
          uiLabel: a.agent_name,
          backendLabel: a.agent_name,
          desc: a.description || "",
        }))
      );
    };
  
    window.addEventListener("refreshAgents", refreshAgents);
    return () => window.removeEventListener("refreshAgents", refreshAgents);
  }, []);
  
  // 🔹 Auto-load latest custom workflow after save/generate
  useEffect(() => {
    const onSaved = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const userId = session?.user?.id;
      if (!userId) return;
      
      const { data } = await supabase
        .from("workflows")
        .select("name")
        .eq("user_id", userId)
        .order("created_at", { ascending: false })
        .limit(1)
        .maybeSingle();

      if (data?.name) {
        await loadWorkflowFromDB(data.name);
      }
    };

    window.addEventListener("workflow-saved", onSaved);
    return () => window.removeEventListener("workflow-saved", onSaved);
  }, [supabase]);


  useEffect(() => {
    function handleLoadWorkflowGraph(e: any) {
      const wf = e.detail;
      if (!wf) return;
      setNodes(wf.nodes || []);
      setEdges(wf.edges || []);
    }
  
    window.addEventListener("loadWorkflowGraph", handleLoadWorkflowGraph);
    return () =>
      window.removeEventListener("loadWorkflowGraph", handleLoadWorkflowGraph);
  }, []);

  useEffect(() => {
    if (showInstrumentPicker) {
      fetchValidationInstruments();
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [showInstrumentPicker]);
  


  /* ---------- Default Verify Loop ---------- */
  useEffect(() => {
    const n: Node<AgentNodeData>[] = [
      { id: "spec", type: "agentNode", position: { x: 60, y: 180 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
      { id: "rtl", type: "agentNode", position: { x: 300, y: 180 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
      { id: "tb", type: "agentNode", position: { x: 540, y: 180 }, data: { uiLabel: "Verification Agent", backendLabel: "Digital Testbench Agent" } },
      { id: "sim", type: "agentNode", position: { x: 780, y: 180 }, data: { uiLabel: "Sim Agent", backendLabel: "Digital Sim Agent" } },
    ];
    const e: Edge[] = [
      { id: "e-spec-rtl", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      { id: "e-rtl-tb", source: "rtl", target: "tb", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      { id: "e-tb-sim", source: "tb", target: "sim", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
    ];
    setNodes(n);
    setEdges(e);
  }, []);

  /* ---------- Drag & Drop ---------- */
  const onDragStartAgent = (ev: React.DragEvent, item: CatalogItem) => {
    ev.dataTransfer.setData("application/reactflow", JSON.stringify(item));
    ev.dataTransfer.effectAllowed = "move";
  };

  const onDragOverCanvas = (ev: React.DragEvent) => {
    ev.preventDefault();
    ev.dataTransfer.dropEffect = "move";
  };

  const onDropCanvas = useCallback(
    async (ev: React.DragEvent) => {
      ev.preventDefault();
      const raw = ev.dataTransfer.getData("application/reactflow");
      if (!raw) return;
      const agent: CatalogItem = JSON.parse(raw);

      const bounds = (ev.currentTarget as HTMLDivElement).getBoundingClientRect();
      const position = rf.project({ x: ev.clientX - bounds.left, y: ev.clientY - bounds.top });

      const id = `${agent.uiLabel}-${Date.now()}`;
      const newNode: Node<AgentNodeData> = {
        id,
        type: "agentNode",
        position,
        data: { uiLabel: agent.uiLabel, backendLabel: agent.backendLabel, desc: agent.desc },
      };

      setNodes((nds) => nds.concat(newNode));

      try {
        const res = await fetch(`${API_BASE}/suggest_next_agent`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ outputs: [agent.backendLabel], domain: loop })
        });
        const j = await res.json();
        console.log("Suggested connection:", j);
      } catch (e) {
        console.warn("Suggestion failed", e);
      }
      setEdges((eds) => {
        if (nodes.length === 0) return eds;
        const lastNode = getRightMostNode(nodes);
        if (!lastNode) return eds;
        const newEdge: Edge = {
          id: `e-${lastNode.id}-${id}`,
          source: lastNode.id,
          target: id,
          animated: true,
          style: { stroke: "#22d3ee", strokeWidth: 2 },
        };
        return eds.concat(newEdge);
      });
    },
    [rf, nodes, setNodes, setEdges]
  );

  const getRightMostNode = (nds: Node[]) => {
    if (!nds.length) return null;
    return nds.reduce((acc, n) => (n.position.x > acc.position.x ? n : acc), nds[0]);
  };

  const onConnect = useCallback(
    (params: Connection | Edge) => setEdges((eds) => addEdge({ ...params, animated: true, style: { stroke: "#22d3ee" } }, eds)),
    [setEdges]
  );

  /* ---------- Actions ---------- */
  const runWorkflow = async () => {
    // 1) Require user to pick a workflow first
    if (!selectedWorkflowName) {
      alert("Please select a Custom Workflow from the sidebar first.");
      return;
    }
    // Defensive: ensure canvas populated
    // 2) If the canvas is empty, try reloading the workflow (defensive)
    if (!nodes.length) {
      const wfName = selectedWorkflowName;
      console.log("Canvas empty, reloading workflow:", wfName);
      await loadWorkflowFromDB(wfName);
    }

    // ✅ Save-as prompt for every run
    const proposed = defaultRunName(selectedWorkflowName);
    const rn = prompt("💾 Save this run as:", proposed) || "";
    const runName = rn.trim();
    if (!runName) return;

    setPendingRunName(runName);

    const wfNameLower = selectedWorkflowName.toLowerCase();

    const loopLower = ((selectedWorkflowLoopType || loop) || "").toLowerCase();


    // ✅ special-case: create bench does NOT require spec and does NOT need bench picker
    const isCreateBench = wfNameLower.includes("validation_create_bench");

    // ✅ bench picker is only for preflight/hardware run workflows (not create-bench)
    const needsBench =
      wfNameLower.includes("validation_hardware_test_run") ||
      wfNameLower.includes("preflight") ||
      wfNameLower.includes("hardware_test_run");
      wfNameLower.includes("validation_pattern_detection") ||
      wfNameLower.includes("validation_evolution_proposal") ||
      wfNameLower.includes("validation_coverage_proposal") ||
      wfNameLower.includes("validation_apply_proposal") ||

    if (loopLower === "validation" && isCreateBench) {
      // must have saved workflow id
      if (!selectedWorkflowId) {
        alert("Please save/select the workflow first (missing workflow_id).");
        return;
      }

      // build workflow payload (same as your bench picker branch)
      const workflow = {
        loop_type: "validation",
        nodes: nodes.map((n) => ({ label: n.data.backendLabel })),
        edges: edges.map((e) => ({ source: e.source, target: e.target })),
      };

      setPendingWorkflowPayload({
        workflow,
        workflow_id: selectedWorkflowId,
        id: selectedWorkflowId,
      });

     // ✅ no spec for create-bench
      setPendingSpecText("");
      setPendingSpecFile(undefined);

      // ✅ go straight to instrument picker
      setShowInstrumentPicker(true);
      return;
    }

    if (loopLower === "validation" && needsBench) {
      // ✅ existing bench-picker workflows (preflight/hardware_test_run)
      if (!selectedWorkflowId) {
        alert("Please save/select the workflow first (missing workflow_id).");
        return;
      }

      const workflow = {
        loop_type: "validation",
        nodes: nodes.map((n) => ({ label: n.data.backendLabel })),
        edges: edges.map((e) => ({ source: e.source, target: e.target })),
      };

      setPendingWorkflowPayload({
        workflow,
        workflow_id: selectedWorkflowId,
        id: selectedWorkflowId,
      });

      await loadBenches();
      setPendingSpecText("");
      setPendingSpecFile(undefined);
      setShowBenchPicker(true);
      fetchValidationTestPlans();
      return;
    }

  // ✅ WF-1 unchanged (spec-driven)
    setShowSpecModal(true);

  };
  
    
  const saveWorkflowLocal = () => {
    localStorage.setItem("workflow_verify_loop", JSON.stringify({ loop, nodes, edges }));
  };

  const clearWorkflow = () => {
    setNodes([]);
    setEdges([]);
  };

  /* ---------- Derived ---------- */
  const prebuiltAgents = useMemo(() => LOOP_AGENTS[loop], [loop]);

  const prebuiltWorkflows = useMemo(() => {
    const all = {
      digital: ["Verify_Loop", "Spec2RTL"],
      analog: ["Spec2Circuit", "Spec2Sim"],
      embedded: ["Spec2Code", "Spec2Sim"],
      system: ["Digital_IP_Prototype_Loop"],
      validation: [],
    };
    return all[loop] ?? [];
  }, [loop]);

  const loadPrebuiltWorkflow = (wf: string) => {

    setSelectedWorkflowName(wf);
    setSelectedWorkflowId(null);
    setSelectedWorkflowLoopType(loop);
    // clear existing canvas
    setNodes([]);
    setEdges([]);
  
    if (loop === "digital" && wf.includes("Spec2RTL")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
        { id: "rtl",  type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
      ];
      const e: Edge[] = [
        { id: "e-spec-rtl", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
      setNodes(n);
      setEdges(e);
    //  setShowSpecModal(true);
    }
    if (loop === "analog" && wf.includes("Spec2Circuit")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Analog Spec Agent" } },
        { id: "netlist", type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "Netlist Agent", backendLabel: "Analog Netlist Agent" } },
      ];
      const e: Edge[] = [
        { id: "e-spec-netlist", source: "spec", target: "netlist", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
      setNodes(n);
      setEdges(e);
    //  setShowSpecModal(true);
    }
    if (loop === "embedded" && wf.includes("Spec2Code")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Embedded Spec Agent" } },
        { id: "code", type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent" } },
      ];
      const e: Edge[] = [{ id: "e-spec-code", source: "spec", target: "code", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } }];
      setNodes(n);
      setEdges(e);
    // setShowSpecModal(true);
    }
    if (loop === "system" && wf.includes("Digital_IP_Prototype_Loop")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 80, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
        { id: "rtl", type: "agentNode", position: { x: 300, y: 200 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
        { id: "code", type: "agentNode", position: { x: 520, y: 200 }, data: { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent" } },
        { id: "sim", type: "agentNode", position: { x: 740, y: 200 }, data: { uiLabel: "Sim Agent", backendLabel: "Embedded Sim Agent" } },
        { id: "result", type: "agentNode", position: { x: 960, y: 200 }, data: { uiLabel: "Result Agent", backendLabel: "Embedded Result Agent" } },
      ];
    
      const e: Edge[] = [
        { id: "e1", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e2", source: "rtl", target: "code", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e3", source: "code", target: "sim", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e4", source: "sim", target: "result", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
    
      setNodes(n);
      setEdges(e);
    //  setShowSpecModal(true);
    }
  };

  const loadCustomWorkflow = (wfName: string) => {
    const stored = localStorage.getItem(`workflow_${wfName}`);
    if (!stored) return;
    const { nodes, edges } = JSON.parse(stored);
    setNodes(nodes);
    setEdges(edges);
    fitView({ padding: 0.2 });
  };

  const loadCustomWorkflowsFromDB = async () => {

    const userId = await getStableUserId(supabase);
    console.log("🧠 (CustomWork) Loading workflows for:", userId);

    const { data, error } = await supabase
      .from("workflows")
      .select("name, created_at, status")
      .eq("user_id", userId)
      .eq("status", "saved")                 // ✅ ONLY show saved templates
      .order("created_at", { ascending: false });



    if (error) {
      console.error("❌ Error loading workflows:", error);
      return;
    }
   
    // 1) Read local first (for fallback)
    //const localNames = Object.keys(localStorage)
     // .filter((k) => k.startsWith("workflow_"))
    //  .map((k) => k.replace("workflow_", ""));
  
    // 2) Build DB query: include both anonId and NULL
    //let q = supabase
    //  .from("workflows")
     // .select("id, name, created_at, user_id")
     // .order("created_at", { ascending: false });
    
    //if (userId && userId !== "undefined" && userId !== "anonymous") {
    // q = q.or(`user_id.eq.${userId},user_id.is.null`);
    //} else {
    //   q = q.or(`user_id.is.null`);
    //}  

    //const { data, error } = await q;
    //if (error) {
     // console.error("❌ Error loading workflows:", error);
      // fallback to local only
     // setCustomWorkflows([...new Set(localNames)]);
     // return;
    //}
  
    //const dbNames = (data || []).map((wf) => wf.name || `workflow_${wf.id}`);

    const dbRows = (data || []).map((w: any) => ({
      name: w.name,
      loop_type: w.loop_type || inferLoopTypeFromName(w.name),
    }));
    
    setCustomWorkflows(dbRows);
    

    // const dbNames = (data || []).map(w => w.name);

    console.log("📁 Loaded workflows:", dbRows);
    // setCustomWorkflows(dbNames);
  
    // 3) Union (DB ⊎ local), DB first
    //const union = Array.from(new Set([...dbNames, ...localNames]));
    //console.log("📁 Loaded workflows:", union);
    //setCustomWorkflows(union);
  };
  const loadWorkflowFromDB = async (wfName: string) => {
    try {
      // 1) Get user ID (session → anon → fail)
      const userId = await getStableUserId(supabase);  // ✅ unified identity

      console.log(`🧠 Loading workflow: ${wfName} for user: ${userId}`);
 
      if (!userId) {
        console.warn("⚠️ No user ID detected.");
        return;
      }
  

  
      // 2) Fetch workflow record
      const { data, error } = await supabase
        .from("workflows")
        .select("id,loop_type,definitions")
        .eq("user_id", userId)
        .eq("name", wfName)
        .maybeSingle();

        if (!error && data) {
          setSelectedWorkflowId(data.id);
          setSelectedWorkflowLoopType(data.loop_type || null);
        
          // keep your existing logic that loads `definitions` into nodes/edges
        }
  
      console.log("📦 Returned from Supabase:", data);
  
      if (error) {
        console.error("❌ Supabase fetch error:", error.message);
        return;
      }
      if (!data || !data.definitions) {
        console.warn("⚠️ No definitions found for:", wfName);
        return;
      }
  
      const defs = data.definitions;
      const nodes = defs.nodes || [];
      const edges = defs.edges || [];
  
      // 3) Normalize nodes for ReactFlow rendering
      const parsedNodes = (defs.nodes || []).map((n: any, i: number) => ({
        id: n.id || `n${i}`,
        type: "agentNode", // <----- IMPORTANT!!!
        position: n.position || { x: 100 + i * 220, y: 200 },
        data: {
          uiLabel: n.data?.uiLabel || n.data?.label || n.data?.backendLabel || "Agent",
          backendLabel: n.data?.backendLabel || n.data?.uiLabel || "Unknown Agent",
          desc: n.data?.desc || "",
        },
      }));
  
      // 4) Normalize edges
      const parsedEdges = (defs.edges || []).map((e: any, i: number) => ({
        id: e.id || `e${i}`,
        source: e.source || e.from,
        target: e.target || e.to,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      }));
  
      console.log(`✅ Parsed ${parsedNodes.length} nodes & ${parsedEdges.length} edges`);
  
      // 5) Update canvas
      setNodes(parsedNodes);
      setEdges(parsedEdges);
  
      setTimeout(() => {
        fitView({ padding: 0.25, duration: 600 });
        console.log("🎨 fitView executed — workflow rendered");
      }, 50);
  
    } catch (err) {
      console.error("🔥 Unexpected load error:", err);
    }
  };


  const runWorkflowWithFormData = async (workflowPayload: any, text: string, file?: File, instrumentIds?: string[],scopePayload?: any,benchId?: string,testPlanName?:string,previewTestPlanOverride?: any) => {
    const formData = new FormData();

    // ✅ unwrap if caller passed { workflow: {...}, workflow_id: ... }
    const wf = workflowPayload?.workflow ? workflowPayload.workflow : workflowPayload;

    formData.append("workflow", JSON.stringify(wf));

    
    formData.append("spec_text", text || "");
    if (file) formData.append("file", file);

    const userId = await getStableUserId(supabase); // or however you already do it in this file
  
    // ✅ Step 4: attach selected instruments (validation only)
    if (instrumentIds?.length) {
      formData.append("instrument_ids", JSON.stringify(instrumentIds));
    }
    // ✅ NEW: scope selection
    if (scopePayload) {
      formData.append("scope_json", JSON.stringify(scopePayload));
    }

    // ✅ NEW: WF1 override — use preview plan as authoritative test_plan
    if (previewTestPlanOverride) {
      formData.append("preview_test_plan_json", JSON.stringify(previewTestPlanOverride));
    }
    // ✅ NEW: only for WF-2/WF-3
    if (benchId) {
      formData.append("bench_id", benchId);
    }

    if (testPlanName && testPlanName.trim()) {
      formData.append("test_plan_name", testPlanName.trim());
    }
  

    if (selectedWorkflowName === "Validation_Create_Bench") {
      formData.append("bench_name", benchName);
      formData.append("bench_location", benchLocation || "");
    }
    
    const res = await fetch(`${API_BASE}/run_workflow`, {
      method: "POST",
      headers: {
        "x-user-id": userId,
      },
      body: formData,
    });
    
    const result = await res.json();
  
    if (result.workflow_id) {
      const newJobId = result.workflow_id;
      setJobId(newJobId);
      setActiveTab("live");
  
      if (selectedWorkflowName) {
        const rec: RunRecord = {
          run_id: newJobId,
          run_name: pendingRunName || defaultRunName(selectedWorkflowName),
          created_at: new Date().toISOString(),
        };
  
        const next = [rec, ...(runs || [])].slice(0, 100);
        setRuns(next);
        saveRunsForWorkflow(selectedWorkflowName, next);
        setSelectedRunId(newJobId);
      }
  
      setPendingRunName(null);
    } else {
      console.error("❌ Workflow run error:", result);
    }
  };
  
  
  
  const handleSpecSubmit = async (text: string, file?: File) => {
    try {
      if (!nodes.length) {
        alert("Workflow canvas is empty — nothing to run.");
        return;
      }

      const wfNameLower = (selectedWorkflowName || "").toLowerCase();
      const loopLower = (selectedWorkflowLoopType || "").toLowerCase();

      if (loopLower === "validation" && wfNameLower.includes("validation_create_bench")) {
        // create-bench should never require spec
        setPendingSpecText("");
        setPendingSpecFile(undefined);

        // if payload wasn’t set (e.g., modal opened unexpectedly), set it now
        if (!pendingWorkflowPayload && selectedWorkflowId) {
          const workflow = {
            loop_type: "validation",
            nodes: nodes.map((n) => ({ label: n.data.backendLabel })),
            edges: edges.map((e) => ({ source: e.source, target: e.target })),
          };
          setPendingWorkflowPayload({
            workflow,
            workflow_id: selectedWorkflowId,
            id: selectedWorkflowId,
          });
        }

        setShowSpecModal(false);
        setShowBenchPicker(false);
        setShowInstrumentPicker(true);
        return;
      }

  
      // -------------------------------
      // FIX LOOP TYPE
      // -------------------------------
      let finalLoopType = "system";

      // Try reading loop type from saved workflow
      
      const fromSidebarLoop = selectedWorkflowLoopType;
  
      // If workflow came from Supabase sidebar, respect its loop_type
      if (fromSidebarLoop) {
        finalLoopType = fromSidebarLoop;
      } else {
        // Otherwise infer from canvas nodes
        const domains = new Set(
          nodes.map((n) => {
            const lbl = (n.data?.backendLabel || "").toLowerCase();
            if (lbl.includes("digital")) return "digital";
            if (lbl.includes("embedded")) return "embedded";
            if (lbl.includes("analog")) return "analog";
            if (lbl.includes("validation")) return "validation";
            return null;
          }).filter(Boolean)
        );
  
        if (domains.size === 1) {
          finalLoopType = Array.from(domains)[0] as string;
        } else {
          finalLoopType = "system"; // multiple domains → system loop
        }
      }
  
      // Build workflow payload
      const workflow = {
        loop_type: finalLoopType,
        nodes: nodes.map(n => ({
          label: n.data.backendLabel
        })),
        edges: edges.map(e => ({
          source: e.source,
          target: e.target
        })),
      };

      // ✅ Step 3: if validation loop → open picker first, do NOT run yet
      // ✅ Step 3: if validation loop → open picker first, do NOT run yet
      if (finalLoopType === "validation") {
  // IMPORTANT: preview endpoint needs a REAL workflow_id (saved workflow row)
        const savedWorkflowId = selectedWorkflowId;

        if (!savedWorkflowId) {
          alert("Validation preview needs a saved workflow. Please select (or save) a workflow, then click Run Workflow again.");
          return;
        }

        setPendingSpecText(text || "");
        setPendingSpecFile(file);

        // attach workflow_id so preview can work
        setPendingWorkflowPayload({
          workflow,
          workflow_id: savedWorkflowId,
          id: savedWorkflowId, // keep if your fallback uses it
        });

        // ✅ NEW: WF-2/WF-3 should go Bench-first, WF-1 stays Instrument-first
        const wfName = (selectedWorkflowName || "").toLowerCase();

        const needsBench =
          wfName.includes("validation_preflight_bench") ||
          wfName.includes("validation_hardware_test_run") ||
          wfName.includes("preflight") ||
          wfName.includes("hardware_test_run") ||
          wfName.includes("validation_pattern_detection") ||
          wfName.includes("validation_coverage_proposal") ||
          wfName.includes("validation_evoluation_proposal") ||
          wfName.includes("validation_apply_proposal")

        if (needsBench) {
          setShowBenchPicker(true);   // <-- you add this modal/state
          fetchValidationTestPlans();
        } else {
          setShowInstrumentPicker(true); // <-- existing WF-1 behavior unchanged
        }
      
        return;
      }


      const formData = new FormData();
      formData.append("workflow", JSON.stringify(workflow));
      formData.append("spec_text", text || "");
      if (file) formData.append("file", file);
  
      const res = await fetch(`${API_BASE}/run_workflow`, {
        method: "POST",
        body: formData,
      });
  
      const result = await res.json();

      if (result.workflow_id) {
        const newJobId = result.workflow_id;
        setJobId(newJobId);
        setActiveTab("live");
      
        // ✅ append run record (localStorage)
        if (selectedWorkflowName) {
          const rec: RunRecord = {
            run_id: newJobId,
            run_name: pendingRunName || defaultRunName(selectedWorkflowName),
            created_at: new Date().toISOString(),
          };
      
          const next = [rec, ...runs].slice(0, 100); // keep last 100 runs
          setRuns(next);
          saveRunsForWorkflow(selectedWorkflowName, next);
      
          setSelectedRunId(newJobId);
        }
      
        setPendingRunName(null);
      } else {
        console.error("❌ Workflow run error:", result);
      }

    } catch (err) {
      console.error("❌ API call failed:", err);
    }
  };
  
  const extractDutPointsFromSchematic = (schematic: any): string[] => {
    const points = new Set<string>();
    const rails = schematic?.connections?.rails || [];
    const probes = schematic?.connections?.probes || [];
    [...rails, ...probes].forEach((x: any) => {
      (x?.dut_points || []).forEach((p: any) => points.add(String(p)));
    });
    return Array.from(points);
  };
  
  const renderBenchSchematicVisual = (schematic: any) => {
    if (!schematic) return null;
  
    const bench = schematic?.bench || {};
    const dut = schematic?.dut || { name: "DUT" };
    const instruments = schematic?.instruments || [];
    const rails = schematic?.connections?.rails || [];
    const probes = schematic?.connections?.probes || [];
  
    const dutPoints = extractDutPointsFromSchematic(schematic);
    const dutPointList = dutPoints.length ? dutPoints : ["VIN", "VOUT", "GND"];
  
    return (
      <div className="space-y-4">
        {/* Header */}
        <div className="rounded-lg border border-zinc-700 bg-black/30 p-3">
          <div className="text-zinc-200 text-sm">
            <span className="text-cyan-300 font-semibold">Bench:</span>{" "}
            {bench?.name || "Unknown"}
            {bench?.location ? <span className="text-zinc-500"> — {bench.location}</span> : null}
          </div>
          <div className="text-zinc-200 text-sm mt-1">
            <span className="text-cyan-300 font-semibold">DUT:</span>{" "}
            {dut?.name || "DUT"}
          </div>
        </div>
  
        {/* Main visual: Instruments | DUT | Connections */}
        <div className="grid grid-cols-1 md:grid-cols-3 gap-3">
          {/* Instruments */}
          <div className="rounded-lg border border-zinc-700 bg-black/30 p-3">
            <div className="text-cyan-300 font-semibold mb-2">Instruments</div>
            <div className="space-y-2 text-sm">
              {instruments.map((i: any) => (
                <div key={i.instrument_id || i.nickname} className="rounded bg-zinc-900/60 p-2 border border-zinc-800">
                  <div className="text-zinc-100 font-semibold">
                    {i.nickname || i.instrument_type || "Instrument"}
                  </div>
                  <div className="text-[12px] text-zinc-400">
                    {i.model ? `${i.vendor || ""} ${i.model}` : (i.vendor || "")}
                  </div>
                  <div className="text-[11px] text-zinc-500 break-all">
                    {i.resource_string || ""}
                  </div>
                </div>
              ))}
              {(!instruments || instruments.length === 0) && (
                <div className="text-zinc-400 text-sm">No instruments listed.</div>
              )}
            </div>
          </div>
  
          {/* DUT */}
          <div className="rounded-lg border border-cyan-700/60 bg-black/30 p-3">
            <div className="text-cyan-300 font-semibold mb-2">DUT</div>
            <div className="rounded-lg border border-zinc-700 bg-zinc-950/60 p-3">
              <div className="text-zinc-100 font-semibold">{dut?.name || "DUT"}</div>
              {dut?.notes ? <div className="text-[12px] text-zinc-400 mt-1">{dut.notes}</div> : null}
  
              <div className="mt-3 text-[12px] text-zinc-300 font-semibold">DUT Points</div>
              <div className="mt-2 flex flex-wrap gap-2">
                {dutPointList.map((p: string) => (
                  <span
                    key={p}
                    className="text-xs px-2 py-1 rounded bg-zinc-900 text-zinc-200 border border-zinc-700"
                  >
                    {p}
                  </span>
                ))}
              </div>
            </div>
          </div>
  
          {/* Connections */}
          <div className="rounded-lg border border-zinc-700 bg-black/30 p-3">
            <div className="text-cyan-300 font-semibold mb-2">Connections</div>
  
            <div className="text-zinc-200 font-semibold text-sm">Rails</div>
            <div className="mt-2 space-y-2 text-sm">
              {rails.map((r: any, idx: number) => (
                <div key={idx} className="rounded bg-zinc-900/60 p-2 border border-zinc-800">
                  <div className="text-zinc-100 font-semibold">{r.rail_name || "Rail"}</div>
                  <div className="text-[12px] text-zinc-400">
                    PSU: {r?.psu?.instrument_id} CH{r?.psu?.channel ?? "?"}
                  </div>
                  <div className="text-[12px] text-zinc-400">
                    Sense: {r?.sense?.dmm_instrument_id} ({r?.sense?.mode || "vdc"})
                  </div>
                  <div className="text-[12px] text-zinc-500">
                    DUT: {JSON.stringify(r?.dut_points || [])}
                  </div>
                </div>
              ))}
              {rails.length === 0 && <div className="text-zinc-400 text-sm">No rails defined.</div>}
            </div>
  
            <div className="mt-4 text-zinc-200 font-semibold text-sm">Probes</div>
            <div className="mt-2 space-y-2 text-sm">
              {probes.map((p: any, idx: number) => (
                <div key={idx} className="rounded bg-zinc-900/60 p-2 border border-zinc-800">
                  <div className="text-zinc-100 font-semibold">{p.signal_name || "Signal"}</div>
                  <div className="text-[12px] text-zinc-400">
                    Scope: {p?.scope?.instrument_id} CH{p?.scope?.channel ?? "?"}
                  </div>
                  <div className="text-[12px] text-zinc-500">
                    DUT: {JSON.stringify(p?.dut_points || [])}
                  </div>
                </div>
              ))}
              {probes.length === 0 && <div className="text-zinc-400 text-sm">No probes defined.</div>}
            </div>
          </div>
        </div>
      </div>
    );
  };
  
  


  const needsTestPlanName =
  selectedWorkflowName === "Validation_Hardware_Test_Run" ||
  selectedWorkflowName === "Validation_Evolution_Proposal" ||
  selectedWorkflowName === "Validation_Coverage_Proposal" ||
  selectedWorkflowName === "Validation_Apply_Proposal";
  

  
  

  /* =========================
     Render
  ========================= */
  return (
    <main className="h-screen overflow-hidden bg-[#0b0b0c] text-white flex flex-col">
      {/* ===== Top bar ===== */}
      <nav className="w-full flex justify-between items-center px-6 py-4 bg-black/70 backdrop-blur border-b border-slate-800">
        <div
          onClick={() => router.push("/")}
          className="text-2xl font-extrabold text-cyan-400 cursor-pointer"
        >
          CHIPLOOP ⚡
        </div>
        <div className="flex items-center gap-6 text-slate-300">
          <button onClick={() => router.push("/")} className="hover:text-cyan-400 transition">
            Home
          </button>
          <button onClick={() => router.push("/pricing")} className="hover:text-cyan-400 transition">
            Pricing
          </button>
          <button
            onClick={async () => {
              await supabase.auth.signOut();
              router.push("/");
            }}
            className="rounded-lg bg-slate-800 px-4 py-2 hover:bg-slate-700"
          >
            Logout
          </button>
        </div>
      </nav>
  
      <div className="flex flex-1 overflow-hidden">
        {/* ===== Sidebar ===== */}
        <aside className="w-96 bg-slate-900/70 border-r border-slate-800 p-4 flex flex-col overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {/* 🧠 Agentic Tools */}
          <h2 className="text-lg font-bold mb-3 text-cyan-400">Agentic Tools</h2>
          <button
            onClick={() => setShowPlanner(true)}
            className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-600 hover:bg-cyan-500 text-white"
          >
            Design Intent Planner
          </button>
          <button
            onClick={() => setShowAgentPlanner(true)}
            className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-600 hover:bg-cyan-500 text-white"
          >
            System Planner
          </button>
          <div className="border-t border-slate-800 my-3" />
          {/* 🔁 Loop Selector */}
          <div className="mb-4">
            <label className="block text-xs uppercase text-cyan-400 mb-2">Loop</label>
            <select
              value={loop}
              onChange={(e) => setLoop(e.target.value as LoopKey)}
              className="w-full rounded-lg bg-slate-800 border border-slate-700 p-2 text-slate-200"
            >
              <option value="digital">Digital Loop</option>
              <option value="analog">Analog Loop</option>
              <option value="embedded">Embedded Loop</option>
              <option value="system">System Loop</option>
              <option value="validation">Validation Loop</option>
            </select>
          </div>
  
          {/* ===== Divider before Workflows ===== */}
          <div className="border-t border-slate-800 my-3" />
  
          {/* ⚙️ Workflows */}
          <section className="mb-6">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Workflows</h3>
  
            <div className="pl-2">
              <p className="text-sm text-cyan-400 font-medium mb-1">Prebuilt</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-32 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent mb-3">
                {prebuiltWorkflows.map((wf) => (
                  <li
                    key={wf}
                    onClick={() => loadPrebuiltWorkflow(wf)}
                    className="px-2 py-1 rounded hover:bg-slate-800 cursor-pointer"
                  >
                    {wf}
                  </li>
                ))}
              </ul>
          {customWorkflows && customWorkflows.length > 0 && (
            <>
              <p className="text-sm text-cyan-400 font-medium mb-1">Custom</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-60 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">

                {customWorkflows
                  .filter((w) => (w.loop_type || inferLoopTypeFromName(w.name)) === loop)
                  .map((w) => (
                    <button
                      key={w.name}
                      className={`w-full text-left px-2 py-1 rounded text-xs hover:bg-slate-700 ${
                        selectedWorkflowName === w.name ? "bg-slate-700 border border-cyan-400" : ""
                      }`}
                      onClick={() => {
                        setSelectedWorkflowName(w.name);
                        loadWorkflowFromDB(w.name);
                        // ✅ load runs for this workflow (localStorage)
                        const loaded = loadRunsForWorkflow(w.name);
                        setRuns(loaded);
                        // optional: auto-select latest run if exists
                        if (loaded.length > 0) {
                          setSelectedRunId(loaded[0].run_id);
                        } else {
                          setSelectedRunId(null);
                        }
                      }}
                      onContextMenu={(e) => openContextMenu(e, w.name)}
                    >
                      {w.name}
                    </button>
                ))}
               
              </ul>
            </>
          )}
           
            </div>
          </section>
  
          {/* ===== Divider before Agents ===== */}
          <div className="border-t border-slate-800 my-3" />
  
          {/* 🤖 Agents */}
          <section className="mb-6">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Agents</h3>
  
            <div className="pl-2">
              <p className="text-sm text-cyan-400 font-medium mb-1">Prebuilt</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-32 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent mb-3">
                {prebuiltAgents.map((a) => (
                  <li
                    key={a.backendLabel}
                    draggable
                    onDragStart={(e) => onDragStartAgent(e, a)}
                    className="cursor-grab active:cursor-grabbing px-2 py-1 rounded hover:bg-slate-800"
                    title={`${a.uiLabel} — ${a.desc || ""}`}
                  >
                    {a.uiLabel}
                  </li>
                ))}
              </ul>
  
              <p className="text-sm text-cyan-400 font-medium mb-1">Custom</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-48 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
                {customAgents.length ? (
                  customAgents.map((a, idx) => (
                    <li
                      key={`${a.backendLabel}-${idx}`}
                      draggable
                      onDragStart={(e) => onDragStartAgent(e, a)}
                      onContextMenu={(e) => openAgentMenu(e, a.backendLabel)}
                      className="cursor-grab active:cursor-grabbing px-2 py-1 rounded hover:bg-slate-800"
                    >
                      {a.uiLabel}
                    </li>
                  ))
                ) : (
                  <p className="text-xs text-slate-400">No custom agents yet</p>
                )}
              </ul>
            </div>
          </section>

          {/* 🧠 Design Intent Library */}
          <div className="border-t border-slate-800 my-3" />

          <section className="mb-6">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Design Intent Library</h3>

            <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-60 pr-1 pl-3 
                 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
    
              {designIntents.length ? (
                designIntents.map((d, idx) => (
                  <li
                    key={d.id}
                    onClick={(e) => {
                     // Prevent left-click on release after right-click
                      if (designIntentMenu) return;
                      loadDesignIntent(d);
                    }}
                    onContextMenu={(e) => {
                      e.preventDefault();   // block browser menu
                      openDesignIntentMenu(e, d);
                    }}
                    className="px-2 py-1 rounded hover:bg-slate-800 cursor-pointer select-none"
                  >
                    {d.title || `Untitled ${idx+1}`}
                  </li>
                ))
              ) : (
                <p className="text-xs text-slate-400">No design intents yet</p>
              )}
            </ul>
          </section>

  
          {/* 🛍 Marketplace */}
          <div className="mt-auto border-t border-slate-700 pt-3">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Marketplace</h3>
  
            <button
              onClick={() => setShowSubmitMarketplaceModal(true)}
              className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-500 hover:bg-cyan-400 text-white"
            >
              Submit for Review
            </button>
  
            <button
              onClick={() => router.push("/marketplace")}
              className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-500 hover:bg-cyan-400 text-white"
            >
              View Public Marketplace
            </button>
          </div>
        </aside>
  
        {/* ===== Canvas & Console ===== */}
        <section className="flex-1 flex flex-col p-4 overflow-hidden">
          {/* Canvas */}
          <div
            className="relative flex-1 border border-slate-800 rounded-xl overflow-hidden bg-black/60"
            onDrop={onDropCanvas}
            onDragOver={onDragOverCanvas}
          >
            <ReactFlow
              key={nodes.map(n => n.id).join("-")}
              nodes={nodes}
              edges={edges}
              onNodesChange={onNodesChange}
              onEdgesChange={onEdgesChange}
              onConnect={onConnect}
              nodeTypes={{ agentNode: AgentNode }}
              fitView
              defaultEdgeOptions={{ animated: true, style: { stroke: '#22d3ee' } }}
            >
             
              <Controls />
              <Background color="#334155" gap={20} />
            </ReactFlow>
          </div>
  
          {/* Action Buttons */}
          <div className="flex justify-center gap-4 py-4 border-t border-slate-800 bg-black/40 mt-4">
            <button 
              className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400"
              onClick={() => {
                setNodes([]);
                setEdges([]);
              }}
            >
              New Workflow
            </button>
            <button onClick={runWorkflow} className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400">
              Run Workflow
            </button>
            <button
              onClick={async () => {
                const workflowName = prompt("💾 Enter a name for this workflow:", `CanvasFlow_${new Date().toISOString().slice(0, 10)}`);


                //const { data: sessionData } = await supabase.auth.getSession();
                //const anonId = localStorage.getItem("anon_user_id");
                //const userId = sessionData?.session?.user?.id || anonId || "anonymous";

                const userId = await getStableUserId();
            
                await fetch("/api/save_custom_workflow", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify({
                    user_id: userId,
                    name: workflowName.trim(),
                    goal: "",
                    summary: `Workflow created from canvas: ${workflowName}`,
                    loop_type: loop.toLowerCase(),   // ✅ correct loop
                    definitions: { nodes, edges },   // ✅ actual workflow graph!
                    status: "saved",
                  }),
                });
            
                window.dispatchEvent(new Event("refreshWorkflows"));
                alert(`✅ Workflow "${workflowName}" saved successfully.`);
              }}
              className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400"
            >
              Save Workflow
            </button>
            <button onClick={clearWorkflow} className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400">
              Clear
            </button>
          </div>
  
          {/* Workflow Execution Tabs */}
          <div className="border-t border-slate-800 bg-black/70 p-4 mt-2 rounded-md overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            <h3 className="mb-2 text-cyan-400 font-semibold">⚡ Workflow Run updates </h3>
  
            <div className="flex gap-4 border-b border-slate-800 mb-4">
              <button
                onClick={() => setActiveTab("summary")}
                className={`pb-2 ${activeTab === "summary" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Summary
              </button>
              <button
                onClick={() => setActiveTab("live")}
                className={`pb-2 ${activeTab === "live" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Live Feed
              </button>
              <button
                onClick={() => setActiveTab("output")}
                className={`pb-2 ${activeTab === "output" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Output Logs
              </button>
            </div>
  
            <div
              className={`rounded-lg border p-3 transition-all duration-300 ${
                activeTab === "summary" || activeTab === "live" || activeTab === "output"
                  ? "border-cyan-500/60 shadow-[0_0_8px_rgba(34,211,238,0.3)]"
                  : "border-slate-700"
              }`}
            >
              {activeTab === "live" && jobId && <WorkflowConsole jobId={jobId} table="workflows" />}
              {activeTab === "summary" && <div></div>}
              {activeTab === "output" && <div></div>}
            </div>
          </div>
        </section>
      </div>

      {/* ===== Right Panel: Run Management ===== */}
      <aside className="w-[420px] bg-slate-900/60 border-l border-slate-800 p-4 flex flex-col overflow-hidden">
        <div className="flex items-center justify-between mb-3">
          <div>
            <h3 className="text-lg font-bold text-cyan-400">Runs</h3>
            <div className="text-xs text-slate-400">
              {selectedWorkflowName ? `Workflow: ${selectedWorkflowName}` : "Select a workflow to see runs"}
            </div>
          </div>
        </div>
        {/* Runs list */}
        <div className="rounded-lg border border-slate-800 bg-black/30 overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {runs.length === 0 ? (
            <div className="p-3 text-slate-400 text-sm italic">
              No runs yet. Click <b>Run</b> to create one.
            </div>
          ) : (
            <div className="divide-y divide-slate-800">
              {runs.map((r) => (
                <div
                  key={r.run_id}
                  className={`p-3 cursor-pointer ${
                    selectedRunId === r.run_id ? "bg-slate-800/70" : "hover:bg-slate-800/40"
                  }`}
                  onClick={() => {
                    setSelectedRunId(r.run_id);
                    setJobId(r.run_id); // ✅ load this run in console
                    setActiveTab("live");
                  }}
                >
                  <div className="flex items-start justify-between gap-2">
                    <div className="min-w-0">
                      <div className="text-sm font-semibold text-slate-100 truncate">
                        {r.run_name}
                      </div>
                      <div className="text-[11px] text-slate-400 truncate">
                        {new Date(r.created_at).toLocaleString()}
                      </div>
                      <div className="text-[11px] text-slate-500 truncate">
                        id: {r.run_id}
                      </div>
                    </div>

                    <div className="flex gap-2 shrink-0">
                      <button
                        onClick={async (e) => {
                          e.stopPropagation();
                          try {
                            const res = await fetch(`${API_BASE}/workflow/${r.run_id}/download_zip`, { method: "GET" });
                            if (!res.ok) throw new Error("download failed");
                            const blob = await res.blob();
                            const url = window.URL.createObjectURL(blob);
                            const a = document.createElement("a");
                            a.href = url;
                            a.download = `${r.run_name || "run"}_${r.run_id}.zip`;
                            a.click();
                            window.URL.revokeObjectURL(url);
                          } catch (err) {
                            console.error("❌ ZIP download failed:", err);
                            alert("Failed to download ZIP for this run.");
                          }
                        }}
                        className="text-xs px-2 py-1 rounded bg-emerald-700 hover:bg-emerald-600 text-white"
                        title="Download ZIP"
                      >
                        ZIP
                      </button>

                      <button
                        onClick={(e) => {
                          e.stopPropagation();
                          if (!selectedWorkflowName) return;

                          if (!confirm(`Delete run "${r.run_name}"?`)) return;

                          const next = runs.filter((x) => x.run_id !== r.run_id);
                          setRuns(next);
                          saveRunsForWorkflow(selectedWorkflowName, next);

                          if (selectedRunId === r.run_id) {
                            setSelectedRunId(null);
                          }
                        }}
                        className="text-xs px-2 py-1 rounded bg-red-700 hover:bg-red-600 text-white"
                        title="Delete from run history"
                      >
                        Del
                      </button>
                    </div>
                  </div>
                </div>
              ))}
            </div>
          )}
        </div>

        
      </aside>

      {contextMenu && (
        <div
          onMouseLeave={closeContextMenu}
          style={{ top: contextMenu.y, left: contextMenu.x }}
          className="fixed z-50 bg-slate-800 border border-slate-700 rounded-md shadow-lg"
        >
          <button
            onClick={() => setRenameTarget({ oldName: contextMenu.name, newName: "" })}
            className="block w-full text-left px-3 py-2 text-sky-300 hover:bg-slate-700"
          >
           ✏️ Rename “{contextMenu.name}”
          </button>

          <button
            onClick={() => publishCustomWorkflow(contextMenu.name)}
            className="block w-full text-left px-3 py-2 text-sky-300 hover:bg-slate-700"
          >
            📤 Publish “{contextMenu.name}” to Marketplace
          </button>
          <button
            onClick={() => deleteCustomWorkflow(contextMenu.name)}
            className="block w-full text-left px-3 py-2 text-red-400 hover:bg-slate-700"
          >
            🗑 Delete “{contextMenu.name}”
          </button>
        </div>
      )}

      {renameTarget.oldName && (
        <div className="fixed inset-0 bg-black/60 z-50 flex items-center justify-center">
          <div className="bg-slate-900 rounded-xl p-6 shadow-xl w-96">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Rename Workflow</h3>
            <p className="text-sm mb-2 text-slate-400">Old name: {renameTarget.oldName}</p>
            <input
              type="text"
              value={renameTarget.newName}
              onChange={(e) => setRenameTarget({ ...renameTarget, newName: e.target.value })}
              placeholder="Enter new name"
              className="w-full mb-4 rounded-lg bg-slate-800 border border-slate-700 p-2 text-slate-200"
            />
           <div className="flex justify-end gap-2">
              <button
                onClick={() => setRenameTarget({ oldName: "", newName: "" })}
                className="px-4 py-2 rounded bg-slate-700 hover:bg-slate-600"
              >
                Cancel
              </button>
              <button
                onClick={renameCustomWorkflow}
                className="px-4 py-2 rounded bg-cyan-500 text-black font-semibold hover:bg-cyan-400"
              >
                Rename
              </button>
            </div>
          </div>
        </div>
      )}

             {/* Agent context menu */}
      {agentMenu && (
          <div
            className="fixed z-50 bg-slate-800 text-white border border-slate-600 rounded shadow-xl py-1"
            style={{ left: agentMenu.x, top: agentMenu.y }}
            onMouseLeave={closeAgentMenu}
          >
            <button
              className="px-4 py-1 hover:bg-slate-700 w-full text-left"
              onClick={() => renameCustomAgent(agentMenu.name)}
            >
              ✏️ Rename
            </button>
            <button
              className="px-4 py-1 hover:bg-slate-700 w-full text-left"
              onClick={() => publishCustomAgent(agentMenu.name)}
            >
              📤 Publish to Marketplace
            </button>
            <button
              className="px-4 py-1 hover:bg-slate-700 w-full text-left text-red-400"
              onClick={() => deleteCustomAgent(agentMenu.name)}
            >
              🗑 Delete
            </button>
          </div>
      )}

      {designIntentMenu && (
        <div
          className="absolute z-50 bg-slate-900 border border-slate-700 rounded shadow-lg text-xs"
          style={{ top: designIntentMenu.y, left: designIntentMenu.x }}
          onMouseLeave={closeDesignIntentMenu}
        >
          <button
            className="block w-full text-left px-3 py-1 hover:bg-slate-800"
            onClick={() => {
          // Edit = open in Planner with hydration
              openDesignIntentJsonEditor(designIntentMenu.intent);
              closeDesignIntentMenu();
            }}
          >
            Edit
          </button>
          <button
            className="block w-full text-left px-3 py-1 hover:bg-slate-800"
            onClick={() => renameDesignIntent(designIntentMenu.intent)}
          >
            Rename
          </button>
          <button
            className="block w-full text-left px-3 py-1 text-red-400 hover:bg-red-900/40"
            onClick={() => deleteDesignIntent(designIntentMenu.intent)}
          >
            Delete
          </button>
        </div>
      )}

      {showInstrumentPicker && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
          {selectedWorkflowName === "Validation_Create_Bench" && (
            <div className="mb-4 space-y-2">
              <input
                className="w-full border px-2 py-1"
                placeholder="Bench name"
                value={benchName}
                onChange={(e) => setBenchName(e.target.value)}
              />
              <input
                className="w-full border px-2 py-1"
                placeholder="Bench location (optional)"
                value={benchLocation}
                onChange={(e) => setBenchLocation(e.target.value)}
              />
            </div>
          )}

          <div className="w-full max-w-2xl rounded-xl bg-zinc-900 p-5 text-white shadow-xl">
            <div className="flex items-center justify-between">
              <h2 className="text-lg font-semibold">Select instruments for this Validation run</h2>
              <button
                className="rounded px-2 py-1 bg-zinc-800 hover:bg-zinc-700"
                onClick={() => setShowInstrumentPicker(false)}
              >
                ✕
              </button>
            </div>

            {instrumentLoadErr && (
              <div className="mt-3 rounded bg-red-900/40 p-2 text-sm">{instrumentLoadErr}</div>
            )}

            <div className="mt-4 space-y-2">
              {(validationInstruments || []).map((inst: any) => (
                <label key={inst.id} className="flex items-center gap-3 rounded bg-zinc-800/60 p-3">
                  <input
                    type="checkbox"
                    checked={selectedInstrumentIds.includes(inst.id)}
                    onChange={() => toggleInstrument(inst.id)}
                  />
                  <div className="flex-1">
                    <div className="font-medium">
                      {inst.nickname} {inst.is_default ? <span className="text-xs text-cyan-300">(default)</span> : null}
                    </div>
                    <div className="text-xs text-zinc-300">
                      {inst.vendor} {inst.model} • {inst.instrument_type} • {inst.interface} • {inst.resource_string}
                    </div>
                    {inst.scpi_idn && <div className="text-xs text-zinc-400 mt-1">IDN: {inst.scpi_idn}</div>}
                  </div>

                  <button
                    className="rounded bg-zinc-700 px-3 py-1 text-sm hover:bg-zinc-600"
                    onClick={async () => {
                      await fetch(`${API_BASE}/validation/instruments/${inst.id}/probe`, { method: "POST" });
                      await fetchValidationInstruments();
                    }}
                  >
                    Test
                  </button>
                </label>
              ))}
            </div>

            {/* Add instrument mini-form */}
            <div className="mt-5 rounded bg-zinc-800/50 p-3">
              <div className="text-sm font-medium mb-2">Add instrument</div>

              <div className="grid grid-cols-2 gap-2">
                <input
                  className="rounded bg-zinc-900 p-2 text-sm"
                  placeholder="Nickname"
                  value={newInstrument.nickname}
                  onChange={(e) => setNewInstrument(s => ({ ...s, nickname: e.target.value }))}
                />
                <input
                  className="rounded bg-zinc-900 p-2 text-sm"
                  placeholder="Model (e.g. E36312A)"
                  value={newInstrument.model}
                  onChange={(e) => setNewInstrument(s => ({ ...s, model: e.target.value }))}
                />

                {/* Instrument Type */}
                <select
                  className="rounded bg-zinc-900 p-2 text-sm border border-zinc-700"
                  value={newInstrument.instrument_type}
                  onChange={(e) =>
                    setNewInstrument({
                      ...newInstrument,
                      instrument_type: e.target.value,
                    })
                  }
                >
                  <option value="psu">PSU</option>
                  <option value="dmm">DMM</option>
                  <option value="smu">SMU</option>
                  <option value="scope">Scope</option>
                </select>
  
                <input
                  className="col-span-2 rounded bg-zinc-900 p-2 text-sm"
                  placeholder='Resource string (e.g. TCPIP0::192.168.0.10::INSTR)'
                  value={newInstrument.resource_string}
                  onChange={(e) => setNewInstrument(s => ({ ...s, resource_string: e.target.value }))}
                />
              </div>

              <div className="mt-2 flex gap-2">
                <button
                  className="rounded bg-cyan-700 px-3 py-2 text-sm hover:bg-cyan-600"
                  onClick={registerValidationInstrument}
                >
                  Register
                </button>
              </div>
            </div>

            {/* Confirm */}
            <div className="mt-5 flex justify-end gap-2">
              <button
                className="rounded bg-zinc-800 px-4 py-2 text-sm hover:bg-zinc-700"
                onClick={() => setShowInstrumentPicker(false)}
              >
                Cancel
              </button>
              <button
                className="rounded bg-green-700 px-4 py-2 text-sm hover:bg-green-600"
                
                onClick={async () => {
                  if (!selectedInstrumentIds.length) {
                    alert("Select at least one instrument.");
                    return;
                  }
                  const wfNameLower = (selectedWorkflowName || "").toLowerCase();
                  const isCreateBench = wfNameLower.includes("validation_create_bench");

                  const isBenchRun =
                    wfNameLower.includes("validation_preflight_bench") ||
                    wfNameLower.includes("validation_hardware_test_run") ||
                    wfNameLower.includes("preflight") ||
                    wfNameLower.includes("hardware_test_run");
                
                  // ✅ Create Bench: NO spec required, NO preview, run immediately
                  if (isCreateBench) {
                    if (!benchName || !benchName.trim()) {
                      alert("Bench name is required.");
                      return; // keep modal open
                    }
                    if (!pendingWorkflowPayload) {
                      alert("Missing pending workflow payload. Please click Run Workflow again.");
                      return;
                    }
                
                    setShowInstrumentPicker(false);
                
                    // spec_text must be empty for create-bench
                    await runWorkflowWithFormData(
                      pendingWorkflowPayload,
                      "",            // spec text
                      undefined,     // spec file
                      selectedInstrumentIds,
                      undefined,     // scope payload
                      undefined,      // benchId
                      testPlanName,
                      previewTestPlan
                    );
                
                    return;
                  }

                  //✅ Bench runs: also skip spec + preview
                  if (isBenchRun) {
                    if (!pendingWorkflowPayload) {
                      alert("Missing pending workflow payload. Please click Run Workflow again.");
                      return;
                    }
                    setShowInstrumentPicker(false);

                    await runWorkflowWithFormData(
                      pendingWorkflowPayload,
                      "",                 // spec text
                      undefined,          // spec file
                      selectedInstrumentIds,
                      undefined,          // scope
                      selectedBenchId || undefined,// bench_id if you have it (optional)
                      testPlanName,
                      previewTestPlan
                    );
                    return;
                  }
                
                  // ✅ Existing Validation run flow (WF-1): preview → scope modal
                  setShowInstrumentPicker(false);
                
                  if (!pendingWorkflowPayload) {
                    alert("Missing pending workflow payload. Please click Run Workflow again.");
                    return;
                  }

                  setShowInstrumentPicker(false);
                  // ✅ trigger actual workflow execution now
                  if (!pendingWorkflowPayload) {
                    alert("Missing pending workflow payload. Please click Run Workflow again.");
                    return;
                  }

                  // ✅ Phase-0 (Option 1): generate test plan preview, then open scope modal
                  const selectedInstrumentRows = (validationInstruments || []).filter((i: any) =>
                    selectedInstrumentIds.includes(i.id)
                  );

                  setSelectedInstrumentRows(selectedInstrumentRows);

                  const wfId =
                    pendingWorkflowPayload?.workflow_id ||
                    pendingWorkflowPayload?.id ||
                    pendingWorkflowPayload?.workflowId;

                  const dsText = (pendingSpecText || "").trim();

                  if (!wfId) {
                    alert("Missing workflow_id for preview. Please click Run Workflow again.");
                    return;
                  }
                  if (!dsText) {
                    alert("Missing datasheet/spec text. Please paste datasheet in the Spec modal.");
                    return;
                  }

                  console.log("[Preview] wfId =", wfId);
                  console.log("[Preview] datasheet_text length =", dsText.length);
                  const resp = await fetch(`${API_BASE}/validation/test_plan/preview`, {
                    method: "POST",
                    headers: { "Content-Type": "application/json" },
                    body: JSON.stringify({
                      workflow_id: wfId,
                      datasheet_text: dsText,
                      goal: "Create a validation test plan",
                    }),
                  });

                  let data: any;
                  try {
                    data = await resp.json();
                  } catch (e) {
                    const raw = await resp.text().catch(() => "");
                    console.error("[Preview] resp.json() failed. status=", resp.status, "raw=", raw);
                    alert(`Preview response was not JSON (status ${resp.status}). See console.`);
                    return;
                  }

                  
                  if (!resp.ok || data?.status !== "ok") {
                    alert(data?.message || "Failed to generate test plan preview");
                    return;
                  }

                  const plan = data.test_plan;
                  setPreviewTestPlan(plan);
                  // open scope modal (user selects tests/features + sees instrument coverage)
                  setShowScopeModal(true);

                  try {
                    const tests = Array.isArray(plan?.tests) ? plan.tests : [];
                    const allNames = tests.map((t: any) => t?.name).filter(Boolean);
                    setSelectedTestNames(allNames);
                  
                    const missing = computeMissingInstrumentTypes(plan, allNames, selectedInstrumentRows);
                    setMissingInstrumentTypes(missing);
                  } catch (e) {
                    console.error("[Preview] post-processing failed:", e, plan);
                    // modal is already open; user can still proceed or you can show a message later
                    setSelectedTestNames([]);
                    setMissingInstrumentTypes([]);
                  }

                  
                }}
              >
                Use selected instruments
              </button>
            </div>
          </div>
        </div>
      )}

      {showBenchPicker && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/60">
          <div className="w-[700px] max-w-[95vw] rounded-lg bg-zinc-900 p-4 border border-zinc-700">
            <div className="flex items-center justify-between">
              <h3 className="text-lg font-semibold text-white">Select Bench</h3>
              <button className="text-zinc-300 hover:text-white" onClick={() => setShowBenchPicker(false)}>✕</button>
            </div>

            <div className="mt-3">
              <select
                className="w-full rounded bg-zinc-800 border border-zinc-700 p-2 text-white"
                value={selectedBenchId}
                onChange={(e) => setSelectedBenchId(e.target.value)}
              >
                <option value="">-- choose a bench --</option>
                {validationBenches.map((b) => (
                  <option key={b.id} value={b.id}>
                    {b.name} — {b.location || "NA"} ({b.status})
                  </option>
                ))}
              </select>
              {/* NEW: View Schematic */}
              <div className="mt-2 flex justify-end">
                <button
                  className="rounded bg-cyan-700 px-3 py-1.5 text-xs text-white hover:bg-cyan-600 disabled:opacity-50"
                  disabled={!selectedBenchId}
                  onClick={async () => {
                    if (!selectedBenchId) return;
                    await openBenchSchematic(selectedBenchId);
                  }}
                  title={!selectedBenchId ? "Select a bench first" : "View bench schematic"}
                >
                  👁 View Schematic
                </button>
              </div>
            </div>

            {/* ✅ WF4 only: Select Test Plan Name from saved plans */}

            

            {needsTestPlanName  && (
              <div className="mt-4">
                <div className="text-sm text-zinc-200 mb-1">Test Plan (required)</div>

                <select
                  className="w-full rounded bg-zinc-800 border border-zinc-700 p-2 text-white"
                  value={selectedTestPlanId}
                  onChange={(e) => {
                    const id = e.target.value;
                    setSelectedTestPlanId(id);

                    const picked = validationTestPlans.find((p) => p.id === id);
                    if (picked?.name) {
                      setTestPlanName(picked.name); // ✅ this is what backend expects (test_plan_name)
                    }
                  }}
                >
                  <option value="">-- choose a test plan --</option>
                  {validationTestPlans.map((p) => (
                    <option key={p.id} value={p.id}>
                      {p.name}
                    </option>
                  ))}
                </select>

                {/* Optional fallback text input (keep if you want manual entry) */}
                <div className="mt-2">
                  <div className="text-xs text-zinc-400 mb-1">Or type a name (advanced)</div>
                  <input
                    className="w-full rounded border border-zinc-700 bg-black px-2 py-1 text-zinc-100"
                    placeholder="e.g., Baby"
                    value={testPlanName}
                    onChange={(e) => setTestPlanName(e.target.value)}
                  />
                </div>
              </div>
            )}


            <div className="mt-5 flex justify-end gap-2">
              <button className="rounded bg-zinc-800 px-4 py-2 text-sm hover:bg-zinc-700"
                onClick={() => setShowBenchPicker(false)}>
                Cancel
              </button>

              <button className="rounded bg-green-700 px-4 py-2 text-sm hover:bg-green-600"
                onClick={async () => {
                  if (!selectedBenchId) {
                    alert("Select a bench.");
                    return;
                  }
                  if (needsTestPlanName && !testPlanName.trim()) {
                    alert("Enter Test Plan Name (required).");
                    return;
                  }
                  setShowBenchPicker(false);
                  if (!pendingWorkflowPayload) {
                    alert("Missing pending workflow payload. Close and click Run Workflow again.");
                    return;
                  }
                  // For WF-2/WF-3: run preflight/run-validation directly with bench_id
                  await runWorkflowWithFormData(
                    pendingWorkflowPayload,
                    "",
                    undefined,
                    [],                 // instruments not required here
                    null,               // scope_json optional
                    selectedBenchId,      // ✅ add as new param
                    testPlanName,
                    previewTestPlan 
                  );
                }}>
                Use selected bench
              </button>
            </div>
          </div>
        </div>
      )}


      {/* ===== Modals ===== */}
      {showSpecModal && (
        <SpecInputModal
          loop={loop}
          showTestPlanName={selectedWorkflowName === "Validation_Generate_Lab_Handoff"}
          testPlanName={testPlanName}
          setTestPlanName={setTestPlanName}
          onClose={() => setShowSpecModal(false)}
          onSubmit={(text, file) => {
            handleSpecSubmit(text, file);
            setShowSpecModal(false);
            console.log("Spec submitted:", { text, file, testPlanName });
         
          }}
        />
      )}

      {/* NEW: Bench Schematic Viewer Modal */}
      {showBenchSchematicModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
          <div className="w-[1100px] max-w-[96vw] max-h-[92vh] overflow-auto rounded-xl border border-zinc-700 bg-zinc-900 p-4 shadow-2xl">
            <div className="flex items-center justify-between mb-3">
              <div className="text-cyan-300 font-semibold">🔌 Bench Schematic</div>
              <button
                className="text-zinc-300 hover:text-white"
                onClick={() => setShowBenchSchematicModal(false)}
              >
                ✕
              </button>
            </div>

            {benchSchematicErr && (
              <div className="rounded border border-red-700 bg-red-950/40 p-3 text-red-200 text-sm">
                {benchSchematicErr}
              </div>
            )}

            {!benchSchematicErr && benchSchematicModalLoading && (
              <div className="text-zinc-400 text-sm">Loading schematic…</div>
            )}

            {!benchSchematicErr && !benchSchematicModalLoading && benchSchematicObj && (
              <div className="space-y-3">
                {/* Minimal “visual” summary first */}
                <div className="rounded-lg border border-zinc-700 bg-black/30 p-3">
                  <div className="text-zinc-200 text-sm">
                    <span className="text-cyan-300 font-semibold">Bench:</span>{" "}
                    {benchSchematicObj?.bench?.name || "Unknown"}{" "}
                    <span className="text-zinc-500">
                      {benchSchematicObj?.bench?.location ? `— ${benchSchematicObj.bench.location}` : ""}
                    </span>
                  </div>
                  <div className="text-zinc-200 text-sm mt-1">
                    <span className="text-cyan-300 font-semibold">DUT:</span>{" "}
                    {benchSchematicObj?.dut?.name || "DUT"}
                  </div>
                </div>

                {/* Raw JSON (always useful for now) */}

                {renderBenchSchematicVisual(benchSchematicObj)}

                <details className="mt-4 rounded-lg border border-zinc-700 bg-black/30 p-3">
                  <summary className="cursor-pointer text-zinc-200 text-sm font-semibold">
                    Raw JSON (debug)
                  </summary>
                  <pre className="mt-3 text-xs text-zinc-200 whitespace-pre-wrap overflow-auto">
                    {JSON.stringify(benchSchematicObj, null, 2)}
                  </pre>
                </details>
              </div>
            )}
          </div>
        </div>
      )}
  
      {showCreateAgentModal && (
        <CreateAgentModal
          onClose={() => setShowCreateAgentModal(false)}
          onSubmit={(backendLabel, uiLabel, desc) => {
            const next = [...customAgents, { uiLabel, backendLabel, desc }];
            setCustomAgents(next);
            localStorage.setItem("custom_agents", JSON.stringify(next));
          }}
        />
      )}

      {showScopeModal && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/60">
          <div className="w-[900px] max-w-[95vw] rounded-lg bg-zinc-900 p-4 border border-zinc-700">
            <div className="flex items-center justify-between">
              <h3 className="text-lg font-semibold text-white">Validation Scope for this Run</h3>
              <button className="text-zinc-300 hover:text-white" onClick={() => setShowScopeModal(false)}>✕</button>
            </div>

            <div className="mt-3 grid grid-cols-2 gap-4">
              <div className="border border-zinc-700 rounded p-3">
                <div className="text-sm text-zinc-200 mb-2">Select tests/features to include:</div>
                <div className="max-h-[380px] overflow-auto space-y-2">
                  {(previewTestPlan?.tests || []).map((t: any) => {
                    const name = t?.name;
                    if (!name) return null;
                    const checked = selectedTestNames.includes(name);
                    return (
                      <label key={name} className="flex items-start gap-2 text-zinc-100">
                        <input
                          type="checkbox"
                          checked={checked}
                          onChange={(e) => {
                            const next = e.target.checked
                              ? [...selectedTestNames, name]
                              : selectedTestNames.filter((x) => x !== name);
                            setSelectedTestNames(next);

                            // recompute missing
                            const missing = computeMissingInstrumentTypes(previewTestPlan, next, selectedInstrumentRows);
                            setMissingInstrumentTypes(missing);
                          }}
                        />
                        <div>
                          <div className="font-medium">{name}</div>
                          <div className="text-xs text-zinc-400">{t?.objective || ""}</div>
                          <div className="text-xs text-zinc-500">
                            requires: {(t?.required_instruments || []).join(", ")}
                          </div>
                        </div>
                      </label>
                    );
                  })}
                </div>
              </div>

              <div className="border border-zinc-700 rounded p-3">
                <div className="text-sm text-zinc-200 mb-2">Instrument coverage</div>

                {missingInstrumentTypes.length === 0 ? (
                  <div className="text-green-400 text-sm">✅ Your selected instruments cover this scope.</div>
                ) : (
                  <div className="text-yellow-300 text-sm">
                    ⚠ Missing instrument types for selected scope: <b>{missingInstrumentTypes.join(", ")}</b>
                    <div className="text-xs text-zinc-400 mt-2">
                      Either (1) deselect tests requiring these instruments, or (2) register/select matching instruments.
                    </div>
                  </div>
                )}

                <div className="mt-4 flex gap-2">
                  <button
                    className="px-3 py-2 rounded bg-zinc-700 text-white hover:bg-zinc-600"
                    onClick={() => {
                    // go back to instrument selection
                      setShowScopeModal(false);
                      setShowInstrumentPicker(true);
                    }}
                  >
                    Change Instruments
                  </button>

                  <button
                    className="ml-auto px-3 py-2 rounded bg-cyan-600 text-white hover:bg-cyan-500"
                    onClick={async () => {
                      if (!pendingWorkflowPayload) {
                        alert("Missing pending workflow payload. Please click Run Workflow again.");
                        return;
                      }
                      if (selectedTestNames.length === 0) {
                        alert("Please select at least one test.");
                        return;
                      }

                      // Build scope payload for Validation Scope Agent
                      const scopePayload = {
                        mode: "by_test_names",
                        include_tests: selectedTestNames,
                      };

                      // Run the workflow uninterrupted with scope_json
                      await runWorkflowWithFormData(
                        pendingWorkflowPayload,
                        pendingSpecText,
                        pendingSpecFile,
                        selectedInstrumentIds,
                        scopePayload,
                        selectedBenchId || undefined,
                        testPlanName,
                        previewTestPlan
                      );

                      // cleanup
                      setShowScopeModal(false);
                      setPreviewTestPlan(null);
                    }}
                  >
                    Run Selected Scope
                  </button>
                </div>
              </div>
            </div>
          </div>
        </div>
      )}

      
  
      {showPlanner && <PlannerModal onClose={() => setShowPlanner(false)} />}
      {showAgentPlanner && <AgentPlannerModal onClose={() => setShowAgentPlanner(false)} />}
    </main>
  );
  
  
}

/* =========================
   Modals (unchanged)
========================= */
function SpecInputModal({ loop, onClose, onSubmit,showTestPlanName,testPlanName,setTestPlanName }: { loop: string; onClose: () => void; onSubmit: (text: string, file?: File) => void;showTestPlanName?: boolean;testPlanName?: string;setTestPlanName?: (v: string) => void; }) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-2xl rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
      <h2 className="mb-4 text-2xl font-bold text-cyan-400">Enter Spec for {loop.charAt(0).toUpperCase() + loop.slice(1)} Loop</h2>
        {showTestPlanName && (
          <div className="mb-4">
            <label className="mb-2 block text-sm font-medium text-slate-200">
             Test Plan Name (saved)
            </label>
            <input
              className="w-full rounded-lg border border-slate-600 bg-slate-800 p-3 text-slate-100 outline-none focus:ring-2 focus:ring-cyan-500"
              placeholder="e.g., PMIC_Bringup_v1 / PCIe_Smoke_TP"
              value={testPlanName || ""}
              onChange={(e) => setTestPlanName?.(e.target.value)}
            />
            <div className="mt-1 text-xs text-slate-400">
              This name will be stored with the generated test_plan_id in Supabase.
            </div>
          </div>
        )}
        <textarea
          className="mb-4 h-40 w-full rounded-lg border border-slate-600 bg-slate-800 p-4 text-lg outline-none focus:ring-2 focus:ring-cyan-500"
          placeholder={
              loop === "digital"
              ? "Describe the digital module (I/Os, behavior)"
              : loop === "analog"
              ? "Describe the analog circuit (R, C, gain, etc.)"
              : loop === "embedded"
              ? "Describe MCU logic and IO behavior"
              : "Describe System (integrated digital + firmware+Analog) behavior"
          }
          value={text}
          onChange={(e) => setText(e.target.value)}
        />
        <div className="mb-4">
          <label className="mb-2 block text-sm font-medium">Upload Spec Document</label>
          <label htmlFor="file-upload" className="flex w-full cursor-pointer items-center justify-center rounded-lg border-2 border-dashed border-slate-600 bg-slate-800 px-4 py-6 hover:bg-slate-700">
            <svg xmlns="http://www.w3.org/2000/svg" className="mr-2 h-6 w-6 text-cyan-400" fill="none" viewBox="0 0 24 24" stroke="currentColor" strokeWidth={2}>
              <path strokeLinecap="round" strokeLinejoin="round" d="M4 16v1a2 2 0 002 2h12a2 2 0 002-2v-1M12 12V4m0 8l-3-3m3 3l3-3" />
            </svg>
            <span className="text-slate-300">Click to upload</span>
            <input id="file-upload" type="file" accept=".txt,md,pdf" className="hidden" onChange={(e) => setFile(e.target.files?.[0] || null)} />
          </label>
          {file && <p className="mt-2 text-sm text-green-400">📄 {file.name} selected</p>}
        </div>
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">Cancel</button>
          <button
            onClick={() => { onSubmit(text, file || undefined); onClose(); }}
            className="rounded-lg bg-cyan-500 px-6 py-2 font-bold text-black hover:bg-cyan-400"
          >
            Run Spec Agent
          </button>
        </div>
      </div>
    </div>
  );
}

function CreateAgentModal({ onClose, onSubmit }: { onClose: () => void; onSubmit: (backendLabel: string, uiLabel: string, desc: string) => void }) {
  const [backendKey, setBackendKey] = useState("");
  const [uiLabel, setUiLabel] = useState("");
  const [desc, setDesc] = useState("");

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-lg rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
        <h2 className="mb-4 text-2xl font-bold text-cyan-400">Create Custom Agent</h2>
        <input type="text" placeholder='Backend label (e.g. "Digital RTL Agent")' value={backendKey} onChange={(e) => setBackendKey(e.target.value)} className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <input type="text" placeholder='UI label (e.g. "RTL Agent")' value={uiLabel} onChange={(e) => setUiLabel(e.target.value)} className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <textarea placeholder="Describe what this agent does." value={desc} onChange={(e) => setDesc(e.target.value)} className="mb-4 h-28 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">Cancel</button>
          <button onClick={() => { onSubmit(backendKey, uiLabel || backendKey, desc); onClose(); }} className="rounded-lg bg-emerald-500 px-6 py-2 font-bold text-black hover:bg-emerald-400">
            Save Agent
          </button>
        </div>
      </div>
    </div>
  );
}
