"use client";

import { useCallback, useEffect, useState } from "react";
import ReactFlow, {
  Background,
  Controls,
  MiniMap,
  addEdge,
  useEdgesState,
  useNodesState,
  Connection,
  Edge,
  Node,
} from "reactflow";
import { ReactFlowProvider } from "reactflow"; // ✅ added
import "reactflow/dist/style.css";
import AgentNode from "./AgentNode";
import WorkflowConsole from "./WorkflowConsole";
import WorkflowResults from "./WorkflowResults";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";

export default function WorkflowPageWrapper() {
  return (
    <ReactFlowProvider>
      <WorkflowPage />
    </ReactFlowProvider>
  );
}

function WorkflowPage() {
  const supabase = createClientComponentClient();

  const [nodes, setNodes, onNodesChange] = useNodesState<Node[]>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [logs, setLogs] = useState<string[]>([]);
  const [selectedAgent, setSelectedAgent] = useState<string | null>(null);
  const [statusLog, setStatusLog] = useState<string>(""); // ⚠ optional
  const [output, setOutput] = useState<string>(""); // ⚠ optional

  // Initialize agents list and prebuilt workflows (if any)
  useEffect(() => {
    const fetchAgents = async () => {
      const { data, error } = await supabase.from("agents").select("*");
      if (error) {
        console.error("Error fetching agents:", error);
        return;
      }
      console.log("Fetched agents:", data);
    };
    fetchAgents();
  }, [supabase]);

  const onConnect = useCallback(
    (params: Connection | Edge) => setEdges((eds) => addEdge(params, eds)),
    [setEdges]
  );

  const addAgentNode = (agentName: string, x: number, y: number) => {
    const id = `${agentName}-${Date.now()}`;
    const newNode: Node = {
      id,
      type: "default",
      position: { x, y },
      data: { label: agentName },
    };
    setNodes((nds) => [...nds, newNode]);
  };

  const runWorkflow = async () => {
    try {
      setLogs((prev) => [...prev, "🚀 Running workflow..."]);

      const { data, error } = await supabase
        .from("workflows")
        .insert([{ name: "User Workflow", status: "running" }])
        .select();

      if (error) throw error;
      setLogs((prev) => [...prev, "✅ Workflow triggered successfully."]);

      // Simulate backend progress updates
      for (let i = 1; i <= 3; i++) {
        setLogs((prev) => [...prev, `Step ${i}/3 completed...`]);
        await new Promise((res) => setTimeout(res, 1000));
      }

      setLogs((prev) => [...prev, "🎉 Workflow completed successfully!"]);
    } catch (err) {
      console.error(err);
      setLogs((prev) => [...prev, "❌ Workflow failed. Check console."]);
    }
  };

  return (
    <div className="flex flex-col h-screen bg-black text-white">
      {/* Header */}
      <div className="flex justify-between items-center p-4 border-b border-gray-800 bg-black">
        <h1 className="text-2xl font-bold text-cyan-400">CHIPLOOP Workflow</h1>
        <div className="space-x-2">
          <button
            onClick={runWorkflow}
            className="bg-cyan-500 hover:bg-cyan-600 text-black font-semibold py-2 px-4 rounded"
          >
            ▶ Run Workflow
          </button>
          <button
            onClick={() => {
              setNodes([]);
              setEdges([]);
              setLogs([]);
            }}
            className="bg-gray-700 hover:bg-gray-600 text-white font-semibold py-2 px-4 rounded"
          >
            Clear
          </button>
        </div>
      </div>

      {/* Main Layout */}
      <div className="flex flex-1 overflow-hidden">
        {/* Sidebar */}
        <div className="w-64 border-r border-gray-800 overflow-y-auto bg-black p-4">
          <h2 className="text-lg font-semibold mb-2 text-cyan-400">Agents</h2>
          <div className="space-y-2">
            <button
              onClick={() => addAgentNode("Spec Agent", 250, 100)}
              className="block w-full text-left bg-gray-800 hover:bg-gray-700 p-2 rounded"
            >
              📘 Spec Agent
            </button>
            <button
              onClick={() => addAgentNode("RTL Agent", 250, 200)}
              className="block w-full text-left bg-gray-800 hover:bg-gray-700 p-2 rounded"
            >
              ⚙️ RTL Agent
            </button>
            <button
              onClick={() => addAgentNode("Assertion Agent", 250, 300)}
              className="block w-full text-left bg-gray-800 hover:bg-gray-700 p-2 rounded"
            >
              🧩 Assertion Agent
            </button>
            <button
              onClick={() => addAgentNode("Simulation Agent", 250, 400)}
              className="block w-full text-left bg-gray-800 hover:bg-gray-700 p-2 rounded"
            >
              🧪 Simulation Agent
            </button>
          </div>
        </div>

        {/* Canvas */}
        <div className="flex-1 bg-gray-950">
          <ReactFlow
            nodes={nodes}
            edges={edges}
            onNodesChange={onNodesChange}
            onEdgesChange={onEdgesChange}
            onConnect={onConnect}
            fitView
          >
            <Background color="#222" gap={16} />
            <Controls />
            <MiniMap />
          </ReactFlow>
        </div>

        {/* Console */}
        <div className="w-80 border-l border-gray-800 bg-black p-4 overflow-y-auto">
          <WorkflowConsole logs={logs} />
        </div>
      </div>
    </div>
  );
}
