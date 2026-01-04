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
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
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
        prev.map((n) => (n === renameTarget.oldName ? renameTarget.newName : n))
      );
  
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
  
      const res = await fetch(`${API_BASE}/validation/instruments/list?user_id=${encodeURIComponent(userId)}`);
      const j = await res.json();
      if (!res.ok || j.status !== "ok") throw new Error(j.message || "Failed to load instruments");
  
      const items = j.instruments || [];
      setValidationInstruments(items);
  
      // auto-select defaults if present (nice UX)
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
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ user_id: userId, ...newInstrument }),
      });
      const j = await res.json();
      if (!res.ok || j.status !== "ok") throw new Error(j.message || "Register failed");
  
      // refresh list & auto-select newly added
      await fetchValidationInstruments();
      if (j.instrument?.id) {
        setSelectedInstrumentIds((prev) => Array.from(new Set([...prev, j.instrument.id])));
      }
  
      // optional: immediately probe so demo feels real
      if (j.instrument?.id) {
        await fetch(`${API_BASE}/validation/instruments/${j.instrument.id}/probe`, { method: "POST" });
      }
  
      // reset minimal fields
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
        setCustomWorkflows(savedWF.map((k) => k.replace("workflow_", "")));
  
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

    // Open spec input modal (handleSpecSubmit will create the run)
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
      setShowSpecModal(true);
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
      setShowSpecModal(true);
    }
    if (loop === "embedded" && wf.includes("Spec2Code")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Embedded Spec Agent" } },
        { id: "code", type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent" } },
      ];
      const e: Edge[] = [{ id: "e-spec-code", source: "spec", target: "code", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } }];
      setNodes(n);
      setEdges(e);
      setShowSpecModal(true);
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
      setShowSpecModal(true);
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
      .select("name, created_at")
      .eq("user_id", userId)        // ✅ Correct filtering
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

    const dbNames = (data || []).map(w => w.name);

    console.log("📁 Loaded workflows:", dbNames);
    setCustomWorkflows(dbNames);
  
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
        .select("definitions")
        .eq("user_id", userId)
        .eq("name", wfName)
        .maybeSingle();
  
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


  const runWorkflowWithFormData = async (workflowPayload: any, text: string, file?: File, instrumentIds?: string[]) => {
    const formData = new FormData();
    formData.append("workflow", JSON.stringify(workflowPayload));
    formData.append("spec_text", text || "");
    if (file) formData.append("file", file);
  
    // ✅ Step 4: attach selected instruments (validation only)
    if (instrumentIds?.length) {
      formData.append("instrument_ids", JSON.stringify(instrumentIds));
    }
  
    const res = await fetch(`${API_BASE}/run_workflow`, { method: "POST", body: formData });
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
  
        const next = [rec, ...runs].slice(0, 100);
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
  
      // -------------------------------
      // FIX LOOP TYPE
      // -------------------------------
      let finalLoopType = "system";

      // Try reading loop type from saved workflow
      const fromSidebarLoop =
        typeof selectedWorkflow !== "undefined"
          ? (selectedWorkflow as any)?.loop_type
          : null;
  
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
      if (finalLoopType === "validation") {
        setPendingSpecText(text || "");
        setPendingSpecFile(file);
        setPendingWorkflowPayload(workflow);
        setShowInstrumentPicker(true);
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

                {customWorkflows.map((wf) => (
                  <button
                    key={wf}
                    className={`w-full text-left px-2 py-1 rounded text-xs hover:bg-slate-700 ${
                      selectedWorkflowName === wf ? "bg-slate-700 border border-cyan-400" : ""
                    }`}
                    onClick={() => {
                      setSelectedWorkflowName(wf);
                      loadWorkflowFromDB(wf);
                      // ✅ load runs for this workflow (localStorage)
                      const loaded = loadRunsForWorkflow(wf);
                      setRuns(loaded);
                      // optional: auto-select latest run if exists
                      if (loaded.length > 0) {
                        setSelectedRunId(loaded[0].run_id);
                      } else {
                        setSelectedRunId(null);
                      }
                    }}
                    onContextMenu={(e) => openContextMenu(e, wf)}
                  >
                    {wf}
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
                onClick={() => {
                  if (!selectedInstrumentIds.length) {
                    alert("Select at least one instrument.");
                    return;
                  }
                  setShowInstrumentPicker(false);
                  // Now trigger the original run path again (simple pattern: call your run function)
                  // Option A: set a flag like "pendingValidationRun" and handle in useEffect
                  // Option B: directly call your run function here if you have access
                }}
              >
                Use selected instruments
              </button>
            </div>
          </div>
        </div>
      )}

      {/* ===== Modals ===== */}
      {showSpecModal && (
        <SpecInputModal
          loop={loop}
          onClose={() => setShowSpecModal(false)}
          onSubmit={(text, file) => {
            handleSpecSubmit(text, file);
            setShowSpecModal(false);
            console.log("Spec submitted:", { text, file });
          }}
        />
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
      
  
      {showPlanner && <PlannerModal onClose={() => setShowPlanner(false)} />}
      {showAgentPlanner && <AgentPlannerModal onClose={() => setShowAgentPlanner(false)} />}
    </main>
  );
  
  
}

/* =========================
   Modals (unchanged)
========================= */
function SpecInputModal({ loop, onClose, onSubmit }: { loop: string; onClose: () => void; onSubmit: (text: string, file?: File) => void }) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-2xl rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
      <h2 className="mb-4 text-2xl font-bold text-cyan-400">Enter Spec for {loop.charAt(0).toUpperCase() + loop.slice(1)} Loop</h2>
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
