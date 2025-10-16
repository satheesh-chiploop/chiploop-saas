"use client";
// 10-15
import React, { useCallback, useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
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
  ReactFlowProvider,
  useReactFlow,
} from "reactflow";
import "reactflow/dist/style.css";

import AgentNode from "./AgentNode";
import WorkflowConsole from "./WorkflowConsole";

/* =========================
   Types & Constants
========================= */
type LoopKey = "digital" | "analog" | "embedded";
type AgentNodeData = { uiLabel: string; backendLabel: string; desc?: string };

type CatalogItem = { uiLabel: string; backendLabel: string; desc?: string };

const LOOP_AGENTS: Record<LoopKey, CatalogItem[]> = {
  digital: [
    { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent", desc: "Capture design spec & I/Os" },
    { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent", desc: "Generate synthesizable RTL" },
    { uiLabel: "Verification Agent", backendLabel: "Digital Testbench Agent", desc: "Create TB & assertions" },
    { uiLabel: "Sim Agent", backendLabel: "Digital Sim Agent", desc: "Compile & simulate" },
  ],
  analog: [
    { uiLabel: "Spec Agent", backendLabel: "Analog Spec Agent", desc: "Analog specs & targets" },
    { uiLabel: "Netlist Agent", backendLabel: "Analog Netlist Agent", desc: "Schematic/topology" },
    { uiLabel: "Sim Agent", backendLabel: "Analog Sim Agent", desc: "SPICE/AMS runs" },
    { uiLabel: "Result Agent", backendLabel: "Analog Result Agent", desc: "Summarize results" },
  ],
  embedded: [
    { uiLabel: "Spec Agent", backendLabel: "Embedded Spec Agent", desc: "Firmware/SoC reqs" },
    { uiLabel: "Code Agent", backendLabel: "Embedded Code Agent", desc: "Drivers & firmware" },
    { uiLabel: "Sim Agent", backendLabel: "Embedded Sim Agent", desc: "Run harness / co-sim" },
    { uiLabel: "Result Agent", backendLabel: "Embedded Result Agent", desc: "Summarize outputs" },
  ],
};

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

  // modals
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);

  // workflow console tab state
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "output">("summary");

  /* ---------- Auth gate ---------- */
  useEffect(() => {
    (async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (!session) router.push("/login");
      else {
        const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
        const savedWF = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
        setCustomAgents(savedAgents);
        setCustomWorkflows(savedWF.map((k) => k.replace("workflow_", "")));
      }
    })();
  }, [supabase, router]);

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
    (ev: React.DragEvent) => {
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
    const { data, error } = await supabase
      .from("workflows")
      .insert([{ name: "Verify Loop", status: "running", logs: "🚀 Started verify loop...\n" }])
      .select("id")
      .single();

    if (error || !data?.id) return;
    setJobId(data.id as string);
    setActiveTab("live");
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
      digital: ["Verify Loop", "Timing Closure Loop", "Spec → RTL Flow"],
      analog: ["Analog RC Filter", "OpAmp Design Flow", "PLL Verification"],
      embedded: ["Firmware Build Flow", "Co-Sim Integration", "Driver Verification"],
    };
    return all[loop];
  }, [loop]);

  /* =========================
     Render
  ========================= */
  return (
    <main className="min-h-screen bg-[#0b0b0c] text-white flex flex-col">
      {/* Top bar */}
      <nav className="w-full flex justify-between items-center px-6 py-4 bg-black/70 backdrop-blur border-b border-slate-800">
        <div onClick={() => router.push("/")} className="text-2xl font-extrabold text-cyan-400 cursor-pointer">CHIPLOOP ⚡</div>
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

      <div className="flex flex-1 overflow-hidden">
        {/* ===== Sidebar ===== */}
        <aside className="w-full max-w-xs bg-slate-900/70 border-r border-slate-800 p-4 overflow-hidden flex flex-col">
          <div className="mb-3">
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

            <div className="mt-3 max-h-12 overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
              <input
                type="text"
                placeholder="Filter agents..."
                className="w-full bg-slate-800 text-white placeholder-gray-400 rounded-md p-2 border border-slate-700 focus:ring-2 focus:ring-cyan-400"
              />
            </div>
          </div>

          <div className="flex-1 overflow-y-auto pr-1 space-y-4 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            <section>
              <h3 className="text-cyan-400 font-semibold mb-2">Prebuilt Agents</h3>
              <ul className="space-y-1 text-sm text-gray-300 max-h-40 overflow-y-auto pr-1 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
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
            </section>

            <section>
              <h3 className="text-cyan-400 font-semibold mb-2">Custom Agents</h3>
              <button
                onClick={() => setShowCreateAgentModal(true)}
                className="text-sm rounded bg-slate-800 border border-slate-700 px-3 py-1 hover:bg-slate-700"
              >
                + Add New Agent
              </button>
              <ul className="mt-2 space-y-1 text-sm text-gray-300 max-h-40 overflow-y-auto pr-1 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
                {customAgents.length ? (
                  customAgents.map((a, idx) => (
                    <li
                      key={`${a.backendLabel}-${idx}`}
                      draggable
                      onDragStart={(e) => onDragStartAgent(e, a)}
                      className="cursor-grab active:cursor-grabbing px-2 py-1 rounded hover:bg-slate-800"
                    >
                      {a.uiLabel}
                    </li>
                  ))
                ) : (
                  <p className="text-xs text-slate-400">No custom agents yet</p>
                )}
              </ul>
            </section>

            <section>
              <h3 className="text-cyan-400 font-semibold mb-2">Prebuilt Workflows</h3>
              <ul className="space-y-1 text-sm text-gray-300 max-h-40 overflow-y-auto pr-1 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
                {prebuiltWorkflows.map((wf) => (
                  <li key={wf} className="px-2 py-1 rounded hover:bg-slate-800">{wf}</li>
                ))}
              </ul>
            </section>

            <section>
              <h3 className="text-cyan-400 font-semibold mb-2">Custom Workflows</h3>
              <ul className="space-y-1 text-sm text-gray-300 max-h-40 overflow-y-auto pr-1 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
                {customWorkflows.length ? (
                  customWorkflows.map((w) => (
                    <li key={w} className="px-2 py-1 rounded hover:bg-slate-800">{w}</li>
                  ))
                ) : (
                  <p className="text-xs text-slate-400">None created yet</p>
                )}
              </ul>
            </section>
          </div>
        </aside>

        {/* ===== Canvas & Console ===== */}
        <section className="flex-1 flex flex-col p-4">
          <div
            className="relative flex-1 border border-slate-800 rounded-xl overflow-hidden bg-black/60"
            onDrop={onDropCanvas}
            onDragOver={onDragOverCanvas}
          >
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
              <MiniMap pannable zoomable />
              <Controls />
              <Background color="#334155" gap={20} />
            </ReactFlow>
          </div>

          <div className="flex justify-center gap-4 py-4 border-t border-slate-800 bg-black/40 mt-4">
            <button onClick={() => setShowSpecModal(true)} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">+ Add Workflow</button>
            <button onClick={runWorkflow} className="rounded-lg bg-emerald-600 px-4 py-2 font-bold text-white hover:bg-emerald-500">Run Workflow</button>
            <button onClick={saveWorkflowLocal} className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400">Save</button>
            <button onClick={clearWorkflow} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">Clear</button>
          </div>

          {/* ===== Workflow Execution Tabs ===== */}
          <div className="border-t border-slate-800 bg-black/70 p-4 mt-2 rounded-md">
            <h3 className="mb-2 text-cyan-400 font-semibold">⚡ Workflow Execution</h3>

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
            {/* Tab Content Area */}
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

      {/* ===== Modals ===== */}
      {showSpecModal && (
        <SpecInputModal
          onClose={() => setShowSpecModal(false)}
          onSubmit={(text, file) => {
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
    </main>
  );
}

/* =========================
   Modals (unchanged)
========================= */
function SpecInputModal({ onClose, onSubmit }: { onClose: () => void; onSubmit: (text: string, file?: File) => void }) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-2xl rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
        <h2 className="mb-4 text-2xl font-bold text-cyan-400">Enter Spec for Spec2RTL</h2>
        <textarea
          className="mb-4 h-40 w-full rounded-lg border border-slate-600 bg-slate-800 p-4 text-lg outline-none focus:ring-2 focus:ring-cyan-500"
          placeholder="Type your design spec here."
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
