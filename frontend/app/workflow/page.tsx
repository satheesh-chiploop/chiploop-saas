"use client";

import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
//import { createClient } from "@supabase/supabase-js";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs"; 

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
  useReactFlow,
  ReactFlowProvider, 
} from "reactflow";
import "reactflow/dist/style.css";

import AgentNode from "./AgentNode";
import WorkflowConsole from "./WorkflowConsole";
// import WorkflowResults from "./WorkflowResults"; // keep handy if you want to show artifacts

/* =========================
   Types & Setup
========================= */

type LoopKey = "digital" | "analog" | "embedded";

// IMPORTANT: we carry both UI text and backend label
type AgentNodeData = {
  uiLabel: string;
  backendLabel: string;
  desc?: string;
};

type LogEntry = { text: string; type: "info" | "success" | "error" };


const supabase = createClientComponentClient({
  cookieOptions: {
    sameSite: "lax",
    path: "/",
  },
});
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

// Catalog item: pretty text + exact backend label (MUST match backend main.py)
type CatalogItem = { uiLabel: string; backendLabel: string; desc?: string };

/**
 * Agent catalog aligned 1:1 with your backend labels.
 * (Note: the Digital Optimizer backend label is intentionally "Digital Opitmizer Agent")
 */
const LOOP_AGENTS: Record<LoopKey, CatalogItem[]> = {
  digital: [
    { uiLabel: "Spec Agent",          backendLabel: "Digital Spec Agent",            desc: "Natural language → initial design spec" },
    { uiLabel: "RTL Agent",           backendLabel: "Digital RTL Agent",             desc: "Generate synthesizable RTL" },
    { uiLabel: "Optimizer Agent",     backendLabel: "Digital Opitmizer Agent",       desc: "Fix compile errors & improve" }, // matches backend typo
    { uiLabel: "Testbench Agent",     backendLabel: "Digital Testbench Agent",       desc: "Create UVM/DUT environment" },
    { uiLabel: "Arch Doc Agent",      backendLabel: "Digital Arch Doc Agent",        desc: "Architecture / pins / timing docs" },
    { uiLabel: "Integration Doc",     backendLabel: "Digital Integration Doc Agent", desc: "System integration guidance" },
    { uiLabel: "Testcase Agent",      backendLabel: "Digital Testcase Agent",        desc: "Generate tests" },
    { uiLabel: "Assertion Agent",     backendLabel: "Digital Assertion Agent",       desc: "Create SVA/PSL properties" },
    { uiLabel: "Covergroup Agent",    backendLabel: "Digital CoverGroup Agent",      desc: "Functional coverage points" },
    { uiLabel: "Coverage Agent",      backendLabel: "Digital Coverage Agent",        desc: "Line/toggle/FSM coverage" },
    { uiLabel: "Simulation Agent",    backendLabel: "Digital Sim Agent",             desc: "Compile & simulate" }, // backend uses 'Sim Agent'
  ],
  analog: [
    { uiLabel: "Spec Agent",          backendLabel: "Analog Spec Agent",             desc: "Analog spec capture (topology/targets)" },
    { uiLabel: "Netlist Agent",       backendLabel: "Analog Netlist Agent",          desc: "Generate netlist / topology" },
    { uiLabel: "Simulation Agent",    backendLabel: "Analog Sim Agent",              desc: "SPICE/AMS simulation" },
    { uiLabel: "Result Agent",        backendLabel: "Analog Result Agent",           desc: "Summarize/analyze results" },
  ],
  embedded: [
    { uiLabel: "Spec Agent",          backendLabel: "Embedded Spec Agent",           desc: "Firmware/SoC requirements" },
    { uiLabel: "Code Agent",          backendLabel: "Embedded Code Agent",           desc: "Generate firmware/drivers" },
    { uiLabel: "Simulation Agent",    backendLabel: "Embedded Sim Agent",            desc: "Co-sim / run harness" },
    { uiLabel: "Result Agent",        backendLabel: "Embedded Result Agent",         desc: "Summarize/analyze results" },
  ],
};

/* =========================
   Modals
========================= */

function SpecInputModal({
  onClose,
  onSubmit,
}: {
  onClose: () => void;
  onSubmit: (text: string, file?: File) => void;
}) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-2xl rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
        <h2 className="mb-4 text-2xl font-bold text-cyan-400">Enter Spec for Spec2RTL</h2>

        <textarea
          className="mb-4 h-40 w-full rounded-lg border border-slate-600 bg-slate-800 p-4 text-lg outline-none focus:ring-2 focus:ring-cyan-500"
          placeholder="Type your design spec here..."
          value={text}
          onChange={(e) => setText(e.target.value)}
        />

        <div className="mb-4">
          <label className="mb-2 block text-sm font-medium">Upload Spec Document</label>
          <label
            htmlFor="file-upload"
            className="flex w-full cursor-pointer items-center justify-center rounded-lg border-2 border-dashed border-slate-600 bg-slate-800 px-4 py-6 hover:bg-slate-700"
          >
            <svg
              xmlns="http://www.w3.org/2000/svg"
              className="mr-2 h-6 w-6 text-cyan-400"
              fill="none"
              viewBox="0 0 24 24"
              stroke="currentColor"
              strokeWidth={2}
            >
              <path strokeLinecap="round" strokeLinejoin="round" d="M4 16v1a2 2 0 002 2h12a2 2 0 002-2v-1M12 12V4m0 8l-3-3m3 3l3-3" />
            </svg>
            <span className="text-slate-300">Click to upload</span>
            <input
              id="file-upload"
              type="file"
              accept=".txt,.md,.pdf"
              className="hidden"
              onChange={(e) => setFile(e.target.files?.[0] || null)}
            />
          </label>
          {file && <p className="mt-2 text-sm text-green-400">📄 {file.name} selected</p>}
        </div>

        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">
            Cancel
          </button>
          <button
            onClick={() => {
              onSubmit(text, file || undefined);
              onClose();
            }}
            className="rounded-lg bg-cyan-500 px-6 py-2 font-bold text-black hover:bg-cyan-400"
          >
            Run Spec Agent
          </button>
        </div>
      </div>
    </div>
  );
}

function CreateAgentModal({
  onClose,
  onSubmit,
}: {
  onClose: () => void;
  onSubmit: (backendKey: string, uiLabel: string, desc: string) => void;
}) {
  const [backendKey, setBackendKey] = useState("");
  const [uiLabel, setUiLabel] = useState("");
  const [desc, setDesc] = useState("");

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-lg rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
        <h2 className="mb-4 text-2xl font-bold text-cyan-400">Create Custom Agent</h2>
        <input
          type="text"
          placeholder='Backend label (e.g., "Digital RTL Agent")'
          value={backendKey}
          onChange={(e) => setBackendKey(e.target.value)}
          className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2"
        />
        <input
          type="text"
          placeholder='UI label (e.g., "RTL Agent")'
          value={uiLabel}
          onChange={(e) => setUiLabel(e.target.value)}
          className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2"
        />
        <textarea
          placeholder="Describe what this agent does..."
          value={desc}
          onChange={(e) => setDesc(e.target.value)}
          className="mb-4 h-28 w-full rounded border border-slate-600 bg-slate-800 p-2"
        />
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">
            Cancel
          </button>
          <button
            onClick={() => {
              onSubmit(backendKey, uiLabel || backendKey, desc);
              onClose();
            }}
            className="rounded-lg bg-emerald-500 px-6 py-2 font-bold text-black hover:bg-emerald-400"
          >
            Save Agent
          </button>
        </div>
      </div>
    </div>
  );
}

/* =========================
   Page
========================= */
export default function WorkflowPageWrapper() {
  // ✅ Wrap your page in the provider
  return (
    <ReactFlowProvider>
      <WorkflowPage />
    </ReactFlowProvider>
  );
}
function WorkflowPage() {
  const router = useRouter();
  const rf = useReactFlow();

  const [loop, setLoop] = useState<LoopKey>("digital");
  const [nodes, setNodes, onNodesChange] = useNodesState<Node<AgentNodeData>>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [statusLog, setStatusLog] = useState<LogEntry[]>([]);
  const [jobId, setJobId] = useState<string | null>(null);

  const [customAgents, setCustomAgents] = useState<CatalogItem[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);

  useEffect(() => {
  let mounted = true;
  const checkSession = async () => {
    const { data: { session } } = await supabase.auth.getSession();
    if (!mounted) return;

    if (session) {
      // ✅ Logged in: load user data
      const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
      const savedWorkflows = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
      setCustomAgents(savedAgents);
      setCustomWorkflows(savedWorkflows.map((k) => k.replace("workflow_", "")));
    } else {
      // 🕐 Wait a bit and recheck before forcing redirect
      setTimeout(async () => {
        const { data: { session: retry } } = await supabase.auth.getSession();
        if (!retry) router.push("/login");
      }, 800); // give cookies time to settle
    }
  };

  checkSession();

  const { data: listener } = supabase.auth.onAuthStateChange((_event, session) => {
    if (session) {
      const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
      const savedWorkflows = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
      setCustomAgents(savedAgents);
      setCustomWorkflows(savedWorkflows.map((k) => k.replace("workflow_", "")));
    } else {
      router.push("/login");
    }
   });

   return () => {
    mounted = false;
    listener.subscription.unsubscribe();
   };
  }, [router]);

  /* ---------- Drag & Drop ---------- */
  const onDragStartAgent = (e: React.DragEvent, item: CatalogItem) => {
    e.dataTransfer.setData("application/agent", JSON.stringify(item));
    e.dataTransfer.effectAllowed = "move";
  };

  const onDragOverCanvas = (e: React.DragEvent) => {
    e.preventDefault();
    e.dataTransfer.dropEffect = "move";
  };

  const onDropCanvas = useCallback(
    (e: React.DragEvent) => {
      e.preventDefault();
      const payload = e.dataTransfer.getData("application/agent");
      if (!payload) return;
      const { uiLabel, backendLabel, desc } = JSON.parse(payload) as CatalogItem;

      const newNode: Node<AgentNodeData> = {
        id: `n_${Date.now()}`,
        type: "agentNode",
        data: { uiLabel, backendLabel, desc },
        position: { x: 80, y: 180 },
      };

      setNodes((nds) => layoutHorizontal([...nds, newNode]));
      setEdges((_eds) => layoutEdges(nodes.concat(newNode).map((n) => n.id)));
      setTimeout(() => rf.fitView({ padding: 0.2 }), 0);
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [nodes]
  );

  /* ---------- Auto layout helpers ---------- */
  function layoutHorizontal(nds: Node<AgentNodeData>[]) {
    const X_START = 80;
    const Y = 180;
    const GAP = 220;
    return nds.map((n, i) => ({ ...n, position: { x: X_START + i * GAP, y: Y } }));
  }

  function layoutEdges(nodeIds: string[]): Edge[] {
    const newEdges: Edge[] = [];
    for (let i = 0; i < nodeIds.length - 1; i++) {
      newEdges.push({
        id: `e_${nodeIds[i]}_${nodeIds[i + 1]}`,
        source: nodeIds[i],
        target: nodeIds[i + 1],
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      });
    }
    return newEdges;
  }

  const onConnect = useCallback(
    (params: Edge | Connection) =>
      setEdges((eds) => addEdge({ ...params, animated: true, style: { stroke: "#22d3ee" } }, eds)),
    []
  );

  /* ---------- Logging helpers ---------- */
  const addLog = (text: string, type: LogEntry["type"] = "info") =>
    setStatusLog((prev) => [...prev, { text, type }]);

  /* ---------- Run workflow ---------- */
  const runWorkflow = async () => {
    setStatusLog([]);
    addLog("🚀 Running Workflow...", "info");

    const needsSpec = nodes.some((n) => n.data?.backendLabel.toLowerCase().includes("spec agent"));
    if (needsSpec) { setShowSpecModal(true); return; }
    await executeWorkflow({});
  };

  const executeWorkflow = async ({ spec, file }: { spec?: string; file?: File }) => {
    addLog("⚡ Executing workflow agents...", "info");

    const graph = {
      loop_type: loop,
      nodes: nodes.map((n) => ({
        id: n.id,
        // BACKEND needs this exact label:
        label: n.data?.backendLabel || n.data?.uiLabel || "",
        ui_label: n.data?.uiLabel || "",
      })),
      edges: edges.map((e) => ({ source: e.source, target: e.target })),
    };

    const form = new FormData();
    form.append("workflow", JSON.stringify(graph));
    if (spec) form.append("spec_text", spec);
    if (file) form.append("file", file);

    const { data: { session } } = await supabase.auth.getSession();
    if (!session) return router.push("/login");

    const res = await fetch(`${API_BASE}/run_workflow`, {
      method: "POST",
      headers: { Authorization: `Bearer ${session.access_token}` },
      body: form,
    });
    const data = await res.json();
    if (data?.run_id) {
      setJobId(String(data.run_id));
      addLog(`✅ Job started: ${String(data.run_id)}`, "success");
    } else {
      addLog("❌ Failed to start job", "error");
    }
  };

  /* ---------- Save / Load (local demo for now) ---------- */
  const saveWorkflowLocal = () => {
    const key = `workflow_${new Date().toISOString()}`;
    const payload = { loop_type: loop, nodes, edges };
    localStorage.setItem(key, JSON.stringify(payload));
    setCustomWorkflows((w) => [key.replace("workflow_", ""), ...w]);
  };

  const clearWorkflow = () => {
    setNodes([]);
    setEdges([]);
    setStatusLog([]);
    setJobId(null);
  };

  /* ---------- UI data ---------- */
  const prebuiltAgents = useMemo(() => LOOP_AGENTS[loop], [loop]);

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white flex flex-col">
      {/* Header */}
      <nav className="w-full flex justify-between items-center px-6 py-4 bg-black/70 backdrop-blur border-b border-slate-800">
        <div onClick={() => router.push("/")} className="text-2xl font-extrabold text-cyan-400 cursor-pointer">
          CHIPLOOP ⚡
        </div>
        <div className="flex items-center gap-6 text-slate-300">
          <button onClick={() => router.push("/")} className="hover:text-cyan-400 transition">Home</button>
          <button onClick={() => router.push("/pricing")} className="hover:text-cyan-400 transition">Pricing</button>
          <button
            onClick={async () => { await supabase.auth.signOut(); router.push("/"); }}
            className="rounded-lg bg-slate-800 px-4 py-2 hover:bg-slate-700"
          >
            Logout
          </button>
        </div>
      </nav>

      {/* Body */}
      <div className="flex flex-1 overflow-hidden">
        {/* Left Sidebar */}
        <aside className="w-full max-w-xs bg-slate-900/70 border-r border-slate-800 p-4 overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {/* Loop selector */}
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
            </select>
          </div>

          {/* Prebuilt Agents */}
          <section className="mb-4">
            <div className="mb-2 text-xs uppercase text-cyan-400">Prebuilt Agents</div>
            <div className="space-y-2 max-h-64 overflow-y-auto pr-1">
              {prebuiltAgents.map((a) => (
                <div
                  key={a.backendLabel}
                  draggable
                  onDragStart={(e) => onDragStartAgent(e, a)}
                  className="cursor-grab rounded-lg border border-slate-700 bg-slate-800 px-3 py-2 hover:bg-slate-700"
                  title={a.desc}
                >
                  {a.uiLabel}
                </div>
              ))}
            </div>
          </section>

          {/* Custom Agents */}
          <section className="mb-4">
            <div className="mb-2 flex items-center justify-between">
              <span className="text-xs uppercase text-cyan-400">Custom Agents</span>
              <button
                onClick={() => setShowCreateAgentModal(true)}
                className="rounded bg-emerald-600 px-2 py-1 text-xs font-bold text-white hover:bg-emerald-500"
              >
                + Add
              </button>
            </div>
            <div className="space-y-2 max-h-44 overflow-y-auto pr-1">
              {customAgents.length === 0 && (
                <div className="text-xs text-slate-500">No custom agents yet.</div>
              )}
              {customAgents.map((a) => (
                <div
                  key={a.backendLabel}
                  draggable
                  onDragStart={(e) => onDragStartAgent(e, a)}
                  className="cursor-grab rounded-lg border border-slate-700 bg-slate-800 px-3 py-2 hover:bg-slate-700"
                  title={a.desc}
                >
                  ✨ {a.uiLabel} <span className="text-slate-500">({a.backendLabel})</span>
                </div>
              ))}
            </div>
          </section>

          {/* Prebuilt Workflows (placeholder; swap to Supabase later) */}
          <section className="mb-4">
            <div className="mb-2 text-xs uppercase text-cyan-400">Prebuilt Workflows</div>
            <div className="space-y-2 max-h-40 overflow-y-auto pr-1">
              <div className="rounded-lg border border-slate-700 bg-slate-800 px-3 py-2 hover:bg-slate-700">
                Verify Loop (Spec → RTL → TB → Sim)
              </div>
              <div className="rounded-lg border border-slate-700 bg-slate-800 px-3 py-2 hover:bg-slate-700">
                Spec→RTL (Spec → RTL → Optimizer)
              </div>
            </div>
          </section>

          {/* My Workflows (local demo) */}
          <section className="mb-4">
            <div className="mb-2 flex items-center justify-between">
              <span className="text-xs uppercase text-cyan-400">My Workflows</span>
              <button
                onClick={saveWorkflowLocal}
                className="rounded bg-cyan-500 px-2 py-1 text-xs font-bold text-black hover:bg-cyan-400"
              >
                Save
              </button>
            </div>
            <div className="space-y-2 max-h-40 overflow-y-auto pr-1">
              {customWorkflows.length === 0 && (
                <div className="text-xs text-slate-500">No saved workflows.</div>
              )}
              {customWorkflows.map((w) => (
                <div key={w} className="rounded-lg border border-slate-700 bg-slate-800 px-3 py-2 hover:bg-slate-700">
                  {w}
                </div>
              ))}
            </div>
          </section>

          {/* Controls */}
          <section className="sticky bottom-0 bg-slate-900/90 backdrop-blur pt-3 border-t border-slate-800">
            <div className="grid grid-cols-2 gap-2">
              <button
                onClick={() => setShowSpecModal(true)}
                className="rounded-lg bg-slate-700 px-3 py-2 hover:bg-slate-600"
              >
                + New Workflow
              </button>
              <button
                onClick={runWorkflow}
                className="rounded-lg bg-emerald-600 px-3 py-2 font-bold text-white hover:bg-emerald-500"
              >
                Run
              </button>
              <button
                onClick={saveWorkflowLocal}
                className="rounded-lg bg-cyan-500 px-3 py-2 font-bold text-black hover:bg-cyan-400"
              >
                Save
              </button>
              <button
                onClick={clearWorkflow}
                className="rounded-lg bg-slate-700 px-3 py-2 hover:bg-slate-600"
              >
                Clear
              </button>
            </div>
          </section>
        </aside>

        {/* Canvas + Logs */}
        <section className="flex-1 flex flex-col">
          {/* Canvas */}
          <div className="relative flex-1" onDrop={onDropCanvas} onDragOver={onDragOverCanvas}>
            <ReactFlow
              nodes={nodes}
              edges={edges}
              onNodesChange={onNodesChange}
              onEdgesChange={onEdgesChange}
              onConnect={onConnect}
              nodeTypes={{ agentNode: AgentNode }}
              fitView
              defaultEdgeOptions={{ animated: true, style: { stroke: "#22d3ee" } }}
            >
              <Background color="#0ea5b7" gap={24} />
              <Controls />
              <MiniMap pannable zoomable />
            </ReactFlow>
          </div>

          {/* Execution Console */}
          <div className="border-t border-slate-800 bg-black/70 p-4">
            <h3 className="mb-2 text-cyan-400 font-semibold">⚡ Workflow Execution</h3>
            {jobId ? (
              <WorkflowConsole jobId={jobId} table="runs" />
            ) : (
              <div className="text-sm text-slate-400">No job started yet.</div>
            )}
            {/* <WorkflowResults results={{}} artifacts={{}} /> */}
          </div>
        </section>
      </div>

      {/* Modals */}
      {showSpecModal && (
        <SpecInputModal
          onClose={() => setShowSpecModal(false)}
          onSubmit={(text, file) => {
            // If Spec Agent present it will use this; otherwise it’s ignored by backend
            executeWorkflow({ spec: text, file });
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
    </main>
  );
}
