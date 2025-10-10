"use client";

import React, { useCallback, useState, useEffect } from "react";
import { useRouter } from "next/navigation";
import WorkflowResults from "./WorkflowResults";
import { supabase } from '@/lib/supabaseClient'
import WorkflowConsole from "./WorkflowConsole";


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
import AgentNodeComponent from "./AgentNode";
type AgentData = {
  label: string;
  desc: string;
};
//type AgentNode = Node<AgentData>;


const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

// --- Supabase workflow helpers ---
async function saveWorkflowToDB(userId: string, name: string, nodes: unknown,edges: unknown) {
  const { error } = await supabase.from("workflows").insert([
    { user_id: userId, name, definition: { nodes, edges } }
  ]);
  if (error) {
    console.error("❌ Save error:", error.message);
    alert("Failed to save workflow");
  } else {
    alert("✅ Workflow saved to Supabase");
  }
}
// eslint-disable-next-line @typescript-eslint/no-unused-vars
async function loadWorkflowsFromDB(userId: string) {
  const { data, error } = await supabase.from("workflows").select("*").eq("user_id", userId);
  if (error) {
    console.error("❌ Load error:", error.message);
    return [];
  }
  return data || [];
}

async function deleteWorkflowFromDB(userId: string, name: string) {
  const { error } = await supabase.from("workflows").delete().eq("user_id", userId).eq("name", name);
  if (error) console.error("❌ Delete error:", error.message);
}


// ---------- Modal for Spec Input ----------
// ---------- Modal for Spec Input ----------
function SpecInputModal({ onClose, onSubmit }: { onClose: () => void; onSubmit: (text: string, file?: File) => void }) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 flex items-center justify-center bg-black/70 z-50">
      <div className="bg-slate-900 p-6 rounded-2xl w-full max-w-2xl shadow-2xl text-slate-100">
        <h2 className="text-2xl font-bold text-cyan-400 mb-4">Enter Spec for Spec2RTL</h2>

        <textarea
          className="w-full h-40 p-4 text-lg rounded-lg bg-slate-800 border border-slate-600 focus:outline-none focus:ring-2 focus:ring-cyan-500 mb-4"
          placeholder="Type your design spec here..."
          value={text}
          onChange={(e) => setText(e.target.value)}
        />

        {/* Custom Upload Box */}
        <div className="mb-4">
          <label className="block text-sm font-medium mb-2">Upload Spec Document</label>
          <label
            htmlFor="file-upload"
            className="flex items-center justify-center w-full px-4 py-6 border-2 border-dashed border-slate-600 rounded-lg cursor-pointer bg-slate-800 hover:bg-slate-700"
          >
            {/* Upload Icon */}
            <svg
              xmlns="http://www.w3.org/2000/svg"
              className="w-6 h-6 text-cyan-400 mr-2"
              fill="none"
              viewBox="0 0 24 24"
              stroke="currentColor"
              strokeWidth={2}
            >
              <path
                strokeLinecap="round"
                strokeLinejoin="round"
                d="M4 16v1a2 2 0 002 2h12a2 2 0 002-2v-1M12 12V4m0 8l-3-3m3 3l3-3"
              />
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
          {file && (
            <p className="mt-2 text-sm text-green-400">📄 {file.name} selected</p>
          )}
        </div>

        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="px-4 py-2 bg-slate-700 hover:bg-slate-600 rounded-lg">
            Cancel
          </button>
          <button
            onClick={() => {
              onSubmit(text, file || undefined);
              onClose();
            }}
            className="px-6 py-2 bg-cyan-500 hover:bg-cyan-400 text-black font-bold rounded-lg"
          >
            Run Spec Agent
          </button>
        </div>
      </div>
    </div>
  );
}
// ---------- Modal for Create Agent ----------
function CreateAgentModal({ onClose, onSubmit }: { onClose: () => void; onSubmit: (name: string, desc: string) => void }) {
  const [name, setName] = useState("");
  const [desc, setDesc] = useState("");

  return (
    <div className="fixed inset-0 flex items-center justify-center bg-black/70 z-50">
      <div className="bg-slate-900 p-6 rounded-2xl w-full max-w-lg shadow-2xl text-slate-100">
        <h2 className="text-2xl font-bold text-cyan-400 mb-4">Create Custom Agent</h2>
        <input
          type="text"
          placeholder="Agent name (e.g., decoder_agent)"
          value={name}
          onChange={(e) => setName(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-800 border border-slate-600"
        />
        <textarea
          placeholder="Describe what this agent does..."
          value={desc}
          onChange={(e) => setDesc(e.target.value)}
          className="w-full h-28 mb-4 p-2 rounded bg-slate-800 border border-slate-600"
        />
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="px-4 py-2 bg-slate-700 hover:bg-slate-600 rounded-lg">Cancel</button>
          <button
            onClick={() => { onSubmit(name, desc); onClose(); }}
            className="px-6 py-2 bg-emerald-500 hover:bg-emerald-400 text-black font-bold rounded-lg"
          >
            Save Agent
          </button>
        </div>
      </div>
    </div>
  );
}
// ---------- Prebuilt agents ----------
const agentList = [
  { type: "spec", label: "Spec Agent", desc: "Natural language → initial design spec" },
  { type: "rtl", label: "RTL Agent", desc: "Generate synthesizable RTL" },
  { type: "opt", label: "Optimizer Agent", desc: "Fix compile errors & improve" },
  { type: "arch", label: "Arch Doc Agent", desc: "Pin & timing documentation" },
  { type: "int", label: "Integration Doc Agent", desc: "System integration guidance" },
  { type: "tb", label: "Testbench Agent", desc: "Builds DUT testbench & stimulus" },
  { type: "tc", label: "Testcase Agent", desc: "Builds Testcases" },
  { type: "sva", label: "Assertion Agent", desc: "Generates assertions (SVA)" },
  { type: "fcov", label: "Covergroup Agent", desc: "Adds covergroups for scenarios" },
  { type: "ccov", label: "Coverage Agent", desc: "Tracks line, toggle, FSM and functional coverage" },
  { type: "sim", label: "Simulation Agent", desc: "Simulation Agent " },
  { type: "reg", label: "Regression Agent", desc: "Runs regressions & aggregates results" },
];

type LogEntry = { text: string; type: "info" | "success" | "error" };

export default function WorkflowPage() {
  // ---------- State ----------
  
  const [nodes, setNodes, onNodesChange] = useNodesState<AgentData>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [statusLog, setStatusLog] = useState<LogEntry[]>([]);
  const [userId, setUserId] = useState<string | null>(null);
  const [output, setOutput] = useState<string>("");
  const [customAgents, setCustomAgents] = useState<{ label: string; desc?: string }[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);
  const [jobId, setJobId] = useState<string | null>(null);
  const router = useRouter();

  useEffect(() => {
  const checkSession = async () => {
    const { data: { session } } = await supabase.auth.getSession();

    if (!session) {
      router.push("/login"); // not logged in → redirect
      return;
    }

    const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
    const savedWorkflows = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
    setCustomAgents(savedAgents);
    setCustomWorkflows(savedWorkflows.map((k) => k.replace("workflow_", "")));
  };
  checkSession();
 }, [router]);

  const onConnect = useCallback((params: Edge | Connection) => setEdges((eds) => addEdge(params, eds)), [setEdges]);

  const addAgentNode = (agent: { label: string; desc?: string }) => {
    const newId = `${nodes.length + 1}`;
    const newNode: Node<AgentData> = {
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

  const addLog = (text: string, type: "info" | "success" | "error" = "info") => {
    setStatusLog((prev) => [...prev, { text, type }]);
  };

  // ---- Run Workflow ----
  const runWorkflow = async () => {
    setStatusLog([]);
    setOutput("");
    addLog("🚀 Running Workflow...", "info");

   const hasSpecAgent = nodes.some((n) => {
       const data = n.data as { label?: string };
       return data.label?.includes("Spec Agent") ?? false;
    });

    if (hasSpecAgent) {
      setShowSpecModal(true);
      return;
    }

    await executeWorkflow({});
  };

const executeWorkflow = async ({ spec, file }: { spec?: string; file?: File }) => {
  addLog("⚡ Executing workflow agents...", "info");

  const graph = {
    nodes: nodes.map((n) => {
      const data = n.data as { label?: string };
      return { id: n.id, label: data.label ?? "" };
    }),
    edges: edges.map((e) => ({ source: e.source, target: e.target })),
  };

  const formData = new FormData();
  formData.append("workflow", JSON.stringify(graph));
  if (spec) formData.append("spec_text", spec);
  if (file) formData.append("file", file);

  try {
    // ✅ fetch Supabase token
    const { data: { session } } = await supabase.auth.getSession();
    if (!session) {
      addLog("❌ Not logged in", "error");
      return;
    }
    const token = session.access_token;

    const res = await fetch(`${API_BASE}/run_workflow`, {
      method: "POST",
      headers: {
        Authorization: `Bearer ${token}`,   // <-- add this
      },
      body: formData,
    });

    if (!res.ok) {
      throw new Error(`HTTP ${res.status}`);
    }

    const data = await res.json();
    addLog("✅ Workflow started", "success");
    setOutput(JSON.stringify(data, null, 2));

// capture job_id from backend
    if (data.job_id) {
      setJobId(data.job_id);
      addLog(`🎯 Tracking job ID: ${data.job_id}`, "info");
    }

  } catch (err: unknown) {
    if (err instanceof Error) {
      addLog(`❌ Workflow failed: ${err.message}`, "error");
    } else {
      addLog("❌ Workflow failed: Unknown error", "error");
    }
  }
};

 // ---- Create Agent ----
  const createAgent = async (name: string, desc: string) => {
    try {
      const formData = new FormData();
      formData.append("agent_name", name);
      formData.append("description", desc);
      const res = await fetch(`${API_BASE}/create_agent`, { method: "POST", body: formData });
      if (!res.ok) {
         throw new Error(`HTTP ${res.status}`);
      }
      await res.json();
      addLog(`✅ Agent '${name}' created`, "success");

      const newAgent = { label: `✨ ${name} Agent`, desc };
      const updated = [...customAgents, newAgent];
      setCustomAgents(updated);
      localStorage.setItem("custom_agents", JSON.stringify(updated));
    } catch (err: unknown) {
      if (err instanceof Error) {
       addLog(`❌ Failed to create agent: ${err.message}`, "error");
      } else {
       addLog("❌ Failed to create agent: Unknown error", "error");
     }
   }
  };

  // ---- Save / Load / Delete Workflows ----
  const saveCurrentWorkflow = async () => {
  const name = prompt("Enter a name to save this workflow:");
  if (!name) return;
  const { data: { session } } = await supabase.auth.getSession();
  if (!session) {
    alert("Not logged in");
    return;
  }
  await saveWorkflowToDB(session.user.id, name, nodes, edges);
  if (!customWorkflows.includes(name)) {
    setCustomWorkflows((prev) => [...prev, name]);
   }
  };


 const loadWorkflowByName = async (name: string) => {
  const { data: { session } } = await supabase.auth.getSession();
  if (!session) return;

  const { data, error } = await supabase
    .from("workflows")
    .select("definition")
    .eq("user_id", session.user.id)
    .eq("name", name)
    .single();

  if (error || !data) return;

  const { nodes: n, edges: e } = data.definition;
  setNodes(n);
  setEdges(e);
  setStatusLog([]);
  setOutput("");
  };

  const deleteWorkflow = async (name: string) => {
  const { data: { session } } = await supabase.auth.getSession();
  if (!session) return;
  await deleteWorkflowFromDB(session.user.id, name);
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

     <header className="flex justify-between items-center px-6 py-4 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="text-center flex-1">
            <h1 className="text-3xl font-bold text-cyan-400">ChipLoop – Agentic AI Platform</h1>
            <p className="text-sm text-slate-400">Build workflows by combining prebuilt/Custom AI agents</p>
       </div>
       <div className="flex space-x-3 absolute right-6 top-4">
          <button
              onClick={() => router.push("/")}
              className="bg-slate-700 hover:bg-slate-600 text-white font-semibold py-2 px-4 rounded"
          >
             🏠 Home
         </button>
         {userId && (
            <button
                 onClick={async () => {
                     const res = await fetch("/api/create-customer-portal-session", { method: "POST" });
                     const data = await res.json();
                     if (data.url) {
                         window.location.href = data.url; // redirect to Stripe portal
                     } else {
                        alert("❌ Failed to open customer portal");
                     }
                }}
                className="bg-emerald-600 hover:bg-emerald-500 text-white font-bold py-2 px-4 rounded"
             >
                Manage Subscription
           </button>
         )}
       <button
           onClick={async () => {
              await supabase.auth.signOut();
              router.push("/");
           }}
           className="bg-red-500 hover:bg-red-400 text-white font-bold py-2 px-4 rounded"
        >
           Logout
       </button>
     </div>
       <button
            onClick={async () => {
            await supabase.auth.signOut()
            router.push('/login')
            }}
           className="ml-4 bg-red-500 hover:bg-red-400 text-white font-bold py-2 px-4 rounded"
        >
          Logout
       </button>
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
          <button onClick={() => setShowCreateAgentModal(true)} className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-emerald-600 hover:bg-emerald-500">
            ➕ Create Agent
          </button>
          {customAgents.map((a) => (
            <div key={a.label} className="flex items-center mb-2">
              <button
                onClick={() => addAgentNode(a)}
                className="flex-1 px-3 py-2 text-left rounded-lg bg-slate-800 hover:bg-slate-700"
              >
                {a.label}
              </button>
              <button onClick={() => deleteAgent(a.label)} className="ml-2 text-red-400 hover:text-red-600">
                ❌
              </button>
            </div>
          ))}

          {/* Prebuilt workflows */}
          <h2 className="text-lg font-bold mt-6 mb-2">Prebuilt Workflows</h2>

          {/* Spec2RTL */}
<button
  onClick={() => {
    setNodes([]);
    setEdges([]);
    setStatusLog([]);
    setOutput("");
    setNodes([
      {
        id: "1",
        type: "agentNode",
        position: { x: 250, y: 0 },
        data: agentList.find((a) => a.type === "spec") as AgentData,
      },
      {
        id: "2",
        type: "agentNode",
        position: { x: 250, y: 120 },
        data: agentList.find((a) => a.type === "rtl") as AgentData,
      },
    ]);
    setEdges([{ id: "e1-2", source: "1", target: "2" }]);
  }}
  className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
>
  📑 Spec2RTL Loop
</button>

{/* RTL Optimizer Loop */}
<button
  onClick={() => {
    setNodes([]);
    setEdges([]);
    setStatusLog([]);
    setOutput("");
    setNodes([
      {
        id: "1",
        type: "agentNode",
        position: { x: 250, y: 0 },
        data: agentList.find((a) => a.type === "spec") as AgentData,
      },
      {
        id: "2",
        type: "agentNode",
        position: { x: 250, y: 120 },
        data: agentList.find((a) => a.type === "rtl") as AgentData,
      },
      {
        id: "3",
        type: "agentNode",
        position: { x: 250, y: 240 },
        data: agentList.find((a) => a.type === "opt") as AgentData,
      },
    ]);
    setEdges([
      { id: "e1-2", source: "1", target: "2" },
      { id: "e2-3", source: "2", target: "3" },
    ]);
  }}
  className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
>
  📑 RTL Optimizer Loop
</button>

          {/* Doc (Integration/Arch) Loop*/}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "arch1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find((a) => a.type === "arch")! },
                { id: "int1", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find((a) => a.type === "int")! },
              ]);
              setEdges([{ id: "e1-2", source: "arch1", target: "int1" }]);
            }}
            className="w-full mb-4 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 Doc (Integration/Arch) Loop
          </button>

          {/* Verify Loop */}
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setStatusLog([]);
              setOutput("");
              setNodes([
                { id: "1", type: "agentNode", position: { x: 250, y: 0 }, data: agentList.find((a) => a.type === "spec")! },
                { id: "2", type: "agentNode", position: { x: 250, y: 120 }, data: agentList.find((a) => a.type === "rtl")! },
                { id: "3", type: "agentNode", position: { x: 250, y: 240 }, data: agentList.find((a) => a.type === "tb")! },
                { id: "4", type: "agentNode", position: { x: 250, y: 360 }, data: agentList.find((a) => a.type === "tc")! },
                { id: "5", type: "agentNode", position: { x: 250, y: 480}, data: agentList.find((a) => a.type === "sva")! },
                { id: "6", type: "agentNode", position: { x: 250, y: 600}, data: agentList.find((a) => a.type === "fcov")! },
                { id: "7", type: "agentNode", position: { x: 250, y: 720}, data: agentList.find((a) => a.type === "sim")! },
                { id: "8", type: "agentNode", position: { x: 250, y: 840}, data: agentList.find((a) => a.type === "ccov")! },
              ]);
              setEdges([
                { id: "e1-2", source: "1", target: "2" },
                { id: "e2-3", source: "2", target: "3" },
                { id: "e3-4", source: "3", target: "4" },
                { id: "e4-5", source: "4", target: "5" },
                { id: "e5-6", source: "5", target: "6" },
                { id: "e5-6", source: "6", target: "7" },
                { id: "e5-6", source: "7", target: "8" },
              ]);
            }}
            className="w-full mb-2 px-3 py-2 text-left rounded-lg bg-indigo-600 hover:bg-indigo-500"
          >
            📑 Verify Loop
          </button>

          {/* Global controls */}
          <button onClick={runWorkflow} className="w-full mb-2 px-3 py-2 rounded-lg bg-green-600 hover:bg-green-500 font-semibold">
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
            ➕ Add newCustom Workflow
          </button>
          <button onClick={saveCurrentWorkflow} className="w-full mb-4 px-3 py-2 rounded-lg bg-blue-600 hover:bg-blue-500">
            💾 Save Current Workflow as…
          </button>

          {/* Custom workflows */}
          <h2 className="text-lg font-bold mt-2 mb-2">My Workflows</h2>
          {customWorkflows.length === 0 && <div className="text-xs text-slate-400 mb-2">(No saved workflows yet)</div>}
          {customWorkflows.map((wf) => (
            <div key={wf} className="flex items-center mb-2">
              <button
                onClick={() => loadWorkflowByName(wf)}
                className="flex-1 px-3 py-2 text-left rounded-lg bg-slate-800 hover:bg-slate-700"
              >
                📁 {wf}
              </button>
              <button onClick={() => deleteWorkflow(wf)} className="ml-2 text-red-400 hover:text-red-600">
                ❌
              </button>
            </div>
          ))}
        </div>

     {/* Canvas */}
{/* Canvas */}
<div className="flex-1 relative">
  <ReactFlow
    nodes={nodes}
    edges={edges}
    nodeTypes={{ agentNode: AgentNodeComponent }}
    onNodesChange={onNodesChange}
    onEdgesChange={onEdgesChange}
    onConnect={onConnect}
    fitView
  >
    <MiniMap />
    <Controls />
    <Background color="#555" gap={16} />
  </ReactFlow>

  {(statusLog.length > 0 || output) && (
    <div className="absolute bottom-0 left-0 right-0 h-64 overflow-auto bg-black/80 text-sm p-3 border-t border-slate-700">
      <h3 className="font-bold mb-2 text-cyan-400">Agent Execution Log</h3>

      {/* Status messages */}
      <ul className="space-y-1">
        {statusLog.map((e, i) => (
          <li
            key={i}
            className={
              e.type === "success"
                ? "text-green-400"
                : e.type === "error"
                ? "text-red-400"
                : "text-yellow-300"
            }
          >
            {e.text}
          </li>
        ))}
      </ul>

      {/* ✅ Workflow Results now inside log box */}
      {output && (
        <div className="mt-3 text-xs">
          <WorkflowResults
            results={JSON.parse(output).workflow_results}
            artifacts={JSON.parse(output).artifacts}
          />
         {jobId && (
          <div className="mt-4">
            <h3 className="font-bold text-cyan-400 mb-1">🔴 Live Execution Feed</h3>
            <WorkflowConsole jobId={jobId} />
           </div>
         )}
        </div>
      )}
    </div>
  )}
</div>   {/* closes flex-1 relative (Canvas) */}
</div>   {/* closes flex flex-1 (Sidebar + Canvas) */}

{showSpecModal && (
  <SpecInputModal
    onClose={() => setShowSpecModal(false)}
    onSubmit={(t, f) => executeWorkflow({ spec: t, file: f })}
  />
)}

{showCreateAgentModal && (
  <CreateAgentModal
    onClose={() => setShowCreateAgentModal(false)}
    onSubmit={createAgent}
  />
)}
</div>   
);        // closes return
}         // closes component