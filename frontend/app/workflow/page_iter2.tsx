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

export default function WorkflowPage() {
  // ---------- State ----------
  const [nodes, setNodes, onNodesChange] = useNodesState<Node[]>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [specText, setSpecText] = useState("");
  const [statusLog, setStatusLog] = useState<string[]>([]);
  const [output, setOutput] = useState<string>(""); // small debug/result panel
  const [customAgents, setCustomAgents] = useState<{ label: string; desc?: string }[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const router = useRouter();

  useEffect(() => {
    const user =
      typeof window !== "undefined" ? localStorage.getItem("chiploop_user") : null;
    if (!user) router.push("/login");

    // Load saved custom agents/workflows
    const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
    const savedWorkflows = Object.keys(localStorage).filter((k) =>
      k.startsWith("workflow_")
    );
    setCustomAgents(savedAgents);
    setCustomWorkflows(savedWorkflows.map((k) => k.replace("workflow_", "")));
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
      setEdges((eds) => [
        ...eds,
        { id: `e${prevId}-${newId}`, source: prevId, target: newId },
      ]);
    }
  };

  // ---- Global: Run Workflow ----
  const runWorkflow = async () => {
    setStatusLog([]);
    setOutput("");
    setStatusLog((prev) => [...prev, "🚀 Running Workflow..."]);

    // Check if workflow has Spec Agent → prompt user
    let specInput = specText;
    const hasSpecAgent = nodes.some((n) => (n.data as any).label.includes("Spec Agent"));
    if (hasSpecAgent) {
      specInput = prompt("Enter your spec (e.g. 4-bit counter with reset):") || "";
    }

    // Prepare compact graph
    const graph = {
      nodes: nodes.map((n) => ({ id: n.id, label: (n.data as any).label })),
      edges: edges.map((e) => ({ source: e.source, target: e.target })),
      spec: specInput || undefined,
    };

    try {
      const res = await fetch("http://127.0.0.1:8000/run_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(graph),
      });
      const data = await res.json();
      setStatusLog((prev) => [...prev, "✅ Workflow completed"]);
      setOutput(JSON.stringify(data, null, 2));
    } catch (err: any) {
      setStatusLog((prev) => [...prev, `❌ Workflow failed: ${err.message}`]);
    }
  };

  // ---- Save / Load / Delete Workflows (localStorage MVP) ----
  const saveCurrentWorkflow = () => {
    const name = prompt("Enter a name to save this workflow:");
    if (!name) return;
    const key = `workflow_${name}`;
    localStorage.setItem(key, JSON.stringify({ nodes, edges }));
    if (!customWorkflows.includes(name)) {
      setCustomWorkflows((prev) => [...prev, name]);
    }
  };

  const loadWorkflowByName = (name: string) => {
    const key = `workflow_${name}`;
    const wfData = localStorage.getItem(key);
    if (wfData) {
      const { nodes: n, edges: e } = JSON.parse(wfData);
      setNodes(n);
      setEdges(e);
      setStatusLog([]);
      setOutput("");
    }
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
        <p className="text-sm text-slate-400">
          Build workflows by combining prebuilt AI agents
        </p>
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

          {/* Prebuilt workflows */}
          <h2 className="text-lg font-bold mt-6 mb-2">Prebuilt Workflows</h2>

          {/* Spec2RTL Loop */}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find(a => a.type === "spec")! },
                { id: "2", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find(a => a.type === "rtl")! },
                { id: "3", type: "agentNode", position: { x: 250, y: 240 }, data: agentList.find(a => a.type === "opt")! },
              ]);
              setEdges([
                { id: "e1-2", source: "1", target: "2" },
                { id: "e2-3", source: "2", target: "3" },
              ]);
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 Spec2RTL Loop
          </button>

          {/* RTL Optimizer Workflow */}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "opt1", type: "agentNode", position: { x: 250, y: 100 }, data: agentList.find(a => a.type === "opt")! },
              ]);
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 RTL Optimizer
          </button>

          {/* Integration Workflow */}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "arch1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find(a => a.type === "arch")! },
                { id: "int1", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find(a => a.type === "int")! },
              ]);
              setEdges([{ id: "e1-2", source: "arch1", target: "int1" }]);
            }}
            className="w-full mb-4 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 Integration Workflow
          </button>

          {/* Verify Loop (unchanged) */}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find((a) => a.type === "tb")! },
                { id: "2", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find((a) => a.type === "sva")! },
                { id: "3", type: "agentNode", position: { x: 250, y: 240 }, data: agentList.find((a) => a.type === "fcov")! },
                { id: "4", type: "agentNode", position: { x: 250, y: 360 }, data: agentList.find((a) => a.type === "ccov")! },
                { id: "5", type: "agentNode", position: { x: 250, y: 480 }, data: agentList.find((a) => a.type === "tpdoc")! },
                { id: "6", type: "agentNode", position: { x: 250, y: 600 }, data: agentList.find((a) => a.type === "reg")! },
              ]);
              setEdges([
                { id: "e1-2", source: "1", target: "2" },
                { id: "e2-3", source: "2", target: "3" },
                { id: "e3-4", source: "3", target: "4" },
                { id: "e4-5", source: "4", target: "5" },
                { id: "e5-6", source: "5", target: "6" },
              ]);
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 Verify Loop
          </button>

          {/* Global Run + Save/Blank */}
          <button
            onClick={runWorkflow}
            className="w-full mb-2 px-3 py-2 rounded-lg bg-green-600 hover:bg-green-500 font-semibold"
          >
            ▶ Run Workflow
          </button>

          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
            }}
            className="w-full mb-2 px-3 py-2 rounded-lg bg-slate-700 hover:bg-slate-600"
          >
            ➕ New Blank Workflow
          </button>

          <button
            onClick={saveCurrentWorkflow}
            className="w-full mb-4 px-3 py-2 rounded-lg bg-blue-600 hover:bg-blue-500"
          >
            💾 Save Current as…
          </button>

          {/* Custom workflows */}
          <h2 className="text-lg font-bold mt-2 mb-2">My Workflows</h2>
          {customWorkflows.length === 0 && (
            <div className="text-xs text-slate-400 mb-2">(No saved workflows yet)</div>
          )}
          {customWorkflows.map((wf) => (
            <div key={wf} className="flex items-center mb-2">
              <button
                onClick={() => loadWorkflowByName(wf)}
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

          {/* Bottom Status log */}
          {statusLog.length > 0 && (
            <div className="absolute bottom-0 left-0 right-0 h-40 overflow-auto bg-black/80 text-green-300 text-sm p-3 border-t border-slate-700">
              <h3 className="font-bold mb-2">Agent Execution Log</h3>
              {statusLog.map((line, i) => (
                <div key={i}>{line}</div>
              ))}
            </div>
          )}

          {/* Small output panel (result/JSON) */}
          {output && (
            <div className="absolute bottom-5 right-5 w-80 h-64 overflow-auto bg-black/80 text-green-300 text-xs p-3 rounded-lg border border-slate-700">
              <h3 className="font-bold mb-2">Workflow Result</h3>
              <pre>{output}</pre>
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
