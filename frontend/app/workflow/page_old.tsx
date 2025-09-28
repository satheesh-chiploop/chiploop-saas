"use client";

import React, { useCallback, useState, useEffect } from "react";
import { useRouter } from "next/navigation";

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
} from "reactflow";

import "reactflow/dist/style.css";
import AgentNode from "./AgentNode"; // custom node

// ---------- Prebuilt agents ----------
const agentList = [
  { type: "spec", label: "📘 Spec Agent", desc: "Natural language → initial design spec" },
  { type: "rtl", label: "💻 RTL Agent", desc: "Generate synthesizable RTL" },
  { type: "opt", label: "🛠 Optimizer Agent", desc: "Fix compile errors & improve" },
  { type: "arch", label: "📐 Arch Doc Agent", desc: "Pin & timing documentation" },
  { type: "int", label: "🔗 Integration Doc Agent", desc: "System integration guidance" },

  // Verification agents
  { type: "tb", label: "🧪 Testbench Agent", desc: "Builds DUT testbench & stimulus" },
  { type: "sva", label: "⚡ Assertion Agent", desc: "Generates assertions (SVA)" },
  { type: "fcov", label: "📊 Functional Coverage Agent", desc: "Adds covergroups for scenarios" },
  { type: "ccov", label: "📑 Code Coverage Agent", desc: "Tracks line, toggle, FSM coverage" },
  { type: "tpdoc", label: "📝 Testplan Doc Agent", desc: "Generates test plan document" },
  { type: "reg", label: "🔁 Regression Agent", desc: "Runs regressions & aggregates results" },
];

// ---------- Prebuilt workflow templates ----------
const templates: Record<string, { nodes: Node[]; edges: Edge[] }> = {
  Spec2RTLLoop: {
    nodes: [
      { id: "1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList[0] },
      { id: "2", type: "agentNode", position: { x: 250, y: 120 }, data: agentList[1] },
      { id: "3", type: "agentNode", position: { x: 250, y: 240 }, data: agentList[2] },
      { id: "4", type: "agentNode", position: { x: 250, y: 360 }, data: agentList[3] },
      { id: "5", type: "agentNode", position: { x: 250, y: 480 }, data: agentList[4] },
    ],
    edges: [
      { id: "e1-2", source: "1", target: "2" },
      { id: "e2-3", source: "2", target: "3" },
      { id: "e3-4", source: "3", target: "4" },
      { id: "e4-5", source: "4", target: "5" },
    ],
  },
  VerifyLoop: {
    nodes: [
      { id: "1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find(a => a.type === "tb")! },
      { id: "2", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find(a => a.type === "sva")! },
      { id: "3", type: "agentNode", position: { x: 250, y: 240 }, data: agentList.find(a => a.type === "fcov")! },
      { id: "4", type: "agentNode", position: { x: 250, y: 360 }, data: agentList.find(a => a.type === "ccov")! },
      { id: "5", type: "agentNode", position: { x: 250, y: 480 }, data: agentList.find(a => a.type === "tpdoc")! },
      { id: "6", type: "agentNode", position: { x: 250, y: 600 }, data: agentList.find(a => a.type === "reg")! },
    ],
    edges: [
      { id: "e1-2", source: "1", target: "2" },
      { id: "e2-3", source: "2", target: "3" },
      { id: "e3-4", source: "3", target: "4" },
      { id: "e4-5", source: "4", target: "5" },
      { id: "e5-6", source: "5", target: "6" },
    ],
  },
};

export default function WorkflowPage() {
  // ---------- State ----------
  const [nodes, setNodes, onNodesChange] = useNodesState<Node[]>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [specText, setSpecText] = useState("");
  const [statusLog, setStatusLog] = useState<string[]>([]);
  const [customAgents, setCustomAgents] = useState<{ label: string; desc?: string }[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const router = useRouter();

  useEffect(() => {
    const user =
      typeof window !== "undefined" ? localStorage.getItem("chiploop_user") : null;
    if (!user) router.push("/login");

    // Load saved custom agents/workflows
    const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
    const savedWorkflows = Object.keys(localStorage).filter(k => k.startsWith("workflow_"));
    setCustomAgents(savedAgents);
    setCustomWorkflows(savedWorkflows.map(k => k.replace("workflow_", "")));
  }, [router]);

  // ---------- Workflow logic ----------
  const onConnect = useCallback(
    (params: Edge | Connection) => setEdges((eds) => addEdge(params, eds)),
    [setEdges]
  );

  const addAgentNode = (agent: { label: string; desc?: string }) => {
    const newId = `${nodes.length + 1}`;
    const newNode: Node = {
      id: newId,
      type: "agentNode",
      data: { label: agent.label, desc: agent.desc || "" },
      position: { x: 250, y: nodes.length * 120 },
    };
    setNodes((nds) => [...nds, newNode]);
    if (nodes.length > 0) {
      const prevId = `${nodes.length}`;
      setEdges((eds) => [...eds, { id: `e${prevId}-${newId}`, source: prevId, target: newId }]);
    }
  };

  const loadTemplate = (name: string) => {
    const tpl = templates[name];
    if (tpl) {
      setNodes(tpl.nodes);
      setEdges(tpl.edges);
    }
  };

  const runSpecAgent = async () => {
    setStatusLog((prev) => [...prev, "🚀 Running Spec Agent..."]);
    try {
      const res = await fetch("http://127.0.0.1:8000/run/spec_agent", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ spec: specText }),
      });
      const data = await res.json();
      if (data.error) {
        setStatusLog((prev) => [...prev, `❌ Error: ${data.error}`]);
      } else {
        setStatusLog((prev) => [
          ...prev,
          `✅ Status: ${data.status}`,
          `📂 RTL saved to backend/design.v`,
        ]);
      }
    } catch (err: any) {
      setStatusLog((prev) => [...prev, `⚠ Failed: ${err.message}`]);
    }
  };

  const saveWorkflow = (name: string) => {
    localStorage.setItem(name, JSON.stringify({ nodes, edges }));
    setCustomWorkflows((prev) => [...prev, name.replace("workflow_", "")]);
  };

  const deleteWorkflow = (name: string) => {
    localStorage.removeItem(`workflow_${name}`);
    setCustomWorkflows((prev) => prev.filter((w) => w !== name));
  };

  const deleteAgent = (label: string) => {
    const updated = customAgents.filter((a) => a.label !== label);
    setCustomAgents(updated);
    localStorage.setItem("custom_agents", JSON.stringify(updated));
  };

  // ---------- UI ----------
  return (
    <div className="flex flex-col h-[100vh] bg-gradient-to-br from-slate-900 via-slate-950 to-black text-slate-100">
      {/* Header */}
      <header className="px-6 py-4 border-b border-slate-800 bg-black/70 backdrop-blur text-center">
        <h1 className="text-3xl font-bold text-cyan-400">ChipLoop – Agentic AI Platform</h1>
        <p className="text-sm text-slate-400">Build workflows by combining prebuilt AI agents</p>
      </header>

      <div className="flex flex-1">
        {/* Sidebar */}
        <div className="w-80 bg-slate-900/70 border-r border-slate-800 p-4 text-slate-200 overflow-y-auto">
          {/* Prebuilt Agents */}
          <h2 className="text-lg font-bold mb-4">Prebuilt Agents</h2>
          {agentList.map((a) => (
            <button
              key={a.type}
              onClick={() => addAgentNode(a)}
              className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-slate-800 hover:bg-slate-700"
            >
              {a.label}
            </button>
          ))}

          {/* Custom Agents */}
          <h2 className="text-lg font-bold mt-6 mb-2">Custom Agents</h2>
          <button
            onClick={() => {
              const name = prompt("Enter new agent name:");
              const desc = prompt("Enter agent description:") || "";
              if (name) {
                const newAgent = { label: name, desc };
                const updated = [...customAgents, newAgent];
                setCustomAgents(updated);
                localStorage.setItem("custom_agents", JSON.stringify(updated));
              }
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-emerald-600 hover:bg-emerald-500"
          >
            ➕ Add Custom Agent
          </button>
          {customAgents.map((a) => (
            <div key={a.label} className="flex items-center mb-2">
              <button
                onClick={() => addAgentNode(a)}
                className="flex-1 px-3 py-2 text-left rounded-lg bg-slate-800 hover:bg-slate-700"
              >
                {a.label}
              </button>
              <button
                onClick={() => deleteAgent(a.label)}
                className="ml-2 text-red-400 hover:text-red-600"
              >
                ❌
              </button>
            </div>
          ))}

          {/* Run Spec Agent (special case) */}
          <div className="p-4 bg-slate-800 rounded-xl mt-6">
            <h2 className="text-lg font-bold mb-2">Run Spec Agent</h2>
            <textarea
              placeholder="Enter spec here (e.g. 4-bit counter with reset)"
              value={specText}
              onChange={(e) => setSpecText(e.target.value)}
              className="w-full mb-2 p-2 rounded bg-slate-900 text-white"
            />
            <button
              onClick={runSpecAgent}
              className="w-full bg-cyan-500 hover:bg-cyan-400 text-black font-bold py-2 px-4 rounded"
            >
              Run Spec Agent
            </button>
          </div>

          {/* Prebuilt workflows */}
          <h2 className="text-lg font-bold mt-6 mb-2">Prebuilt Workflows</h2>
          {Object.keys(templates).map((t) => (
            <button
              key={t}
              onClick={() => loadTemplate(t)}
              className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
            >
              📑 {t}
            </button>
          ))}

          {/* Custom workflows */}
          <h2 className="text-lg font-bold mt-6 mb-2">Custom Workflows</h2>
          <button
            onClick={() => {
              const name = prompt("Enter workflow name:");
              if (name) saveWorkflow(`workflow_${name}`);
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-emerald-600 hover:bg-emerald-500"
          >
            ➕ Add Workflow
          </button>
          {customWorkflows.map((wf) => (
            <div key={wf} className="flex items-center mb-2">
              <button
                onClick={() => {
                  const wfData = localStorage.getItem(`workflow_${wf}`);
                  if (wfData) {
                    const { nodes, edges } = JSON.parse(wfData);
                    setNodes(nodes);
                    setEdges(edges);
                  }
                }}
                className="flex-1 px-3 py-2 text-left rounded-lg bg-slate-800 hover:bg-slate-700"
              >
                📁 {wf}
              </button>
              <button
                onClick={() => deleteWorkflow(wf)}
                className="ml-2 text-red-400 hover:text-red-600"
              >
                ❌
              </button>
            </div>
          ))}
        </div>

        {/* Canvas */}
        <div className="flex-1 relative">
          <ReactFlow
            nodes={nodes}
            edges={edges}
            nodeTypes={{ agentNode: AgentNode }}
            onNodesChange={onNodesChange}
            onEdgesChange={onEdgesChange}
            onConnect={onConnect}
            fitView
          >
            <MiniMap />
            <Controls />
            <Background color="#555" gap={16} />
          </ReactFlow>

          {/* Status log */}
          {statusLog.length > 0 && (
            <div className="absolute bottom-0 left-0 right-0 h-40 overflow-auto bg-black/80 text-green-300 text-sm p-3 border-t border-slate-700">
              <h3 className="font-bold mb-2">Agent Execution Log</h3>
              {statusLog.map((line, i) => (
                <div key={i}>{line}</div>
              ))}
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
