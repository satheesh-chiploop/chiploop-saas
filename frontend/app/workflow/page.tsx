"use client";

import { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";
import ReactFlow, { MiniMap, Controls, Background, useNodesState, useEdgesState, Edge } from "reactflow";
import "reactflow/dist/style.css";
import WorkflowResults from "./WorkflowResults";
import SpecInputModal from "./SpecInputModal";
import CreateAgentModal from "./CreateAgentModal";

// ✅ Supabase setup
const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

interface AgentData {
  label: string;
  desc?: string;
}

interface LogEntry {
  type: "info" | "success" | "error";
  text: string;
}

export default function WorkflowPage() {
  const router = useRouter();

  // ---------- State ----------
  const [nodes, setNodes, onNodesChange] = useNodesState<AgentData>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [statusLog, setStatusLog] = useState<LogEntry[]>([]);
  const [output, setOutput] = useState<string>("");
  const [customAgents, setCustomAgents] = useState<{ label: string; desc?: string }[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);

  // ---------- Auth check ----------
  useEffect(() => {
    const checkSession = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (!session) {
        router.push("/login");
        return;
      }
      const savedAgents = JSON.parse(localStorage.getItem("custom_agents") || "[]");
      const savedWorkflows = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
      setCustomAgents(savedAgents);
      setCustomWorkflows(savedWorkflows.map((k) => k.replace("workflow_", "")));
    };
    checkSession();
  }, [router]);

  // ---------- Helper: Execute workflow ----------
  const executeWorkflow = async ({ spec, file }: { spec: string; file?: File | null }) => {
    try {
      setStatusLog((prev) => [...prev, { type: "info", text: "🚀 Executing workflow..." }]);
      const { data: { session } } = await supabase.auth.getSession();
      const token = session?.access_token;

      const formData = new FormData();
      formData.append("spec_text", spec);
      if (file) formData.append("file", file);

      const res = await fetch("http://209.38.74.151/run_workflow", {
        method: "POST",
        headers: { Authorization: `Bearer ${token}` },
        body: formData,
      });

      const data = await res.json();
      setOutput(JSON.stringify(data, null, 2));
      setStatusLog((prev) => [...prev, { type: "success", text: "✅ Workflow executed successfully!" }]);
    } catch (error: any) {
      setStatusLog((prev) => [...prev, { type: "error", text: "❌ Workflow execution failed." }]);
      console.error(error);
    }
  };

  // ---------- Header actions ----------
  const handleLogout = async () => {
    await supabase.auth.signOut();
    router.push("/");
  };

  const handleManage = async () => {
    try {
      const { data: { session } } = await supabase.auth.getSession();
      const email = session?.user?.email;
      const res = await fetch("http://209.38.74.151/create-customer-portal-session", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ email }),
      });
      const data = await res.json();
      if (data.url) window.location.href = data.url;
      else alert("❌ Failed to open customer portal");
    } catch (err) {
      console.error("Portal error:", err);
    }
  };

  return (
    <div className="flex flex-col h-[100vh] bg-slate-950 text-white">
      {/* ✅ Header Navigation Bar */}
      <div className="flex justify-between items-center bg-slate-900 text-white px-6 py-3 border-b border-slate-700">
        <button
          onClick={() => router.push("/")}
          className="bg-slate-700 hover:bg-slate-600 text-white px-4 py-2 rounded"
        >
          🏠 Home
        </button>
        <div className="flex gap-3">
          <button
            onClick={handleManage}
            className="bg-yellow-500 hover:bg-yellow-400 text-black px-4 py-2 rounded"
          >
            ⚙️ Manage Subscription
          </button>
          <button
            onClick={handleLogout}
            className="bg-red-600 hover:bg-red-500 text-white px-4 py-2 rounded"
          >
            🚪 Logout
          </button>
        </div>
      </div>

      {/* Canvas */}
      <div className="flex-1 relative">
        <ReactFlow
          nodes={nodes}
          edges={edges}
          nodeTypes={{ agentNode: undefined }}
          onNodesChange={onNodesChange}
          onEdgesChange={onEdgesChange}
          fitView
        >
          <MiniMap />
          <Controls />
          <Background color="#555" gap={16} />
        </ReactFlow>

        {statusLog.length > 0 && (
          <div className="absolute bottom-0 left-0 right-0 h-40 overflow-auto bg-black/80 text-sm p-3 border-t border-slate-700">
            <h3 className="font-bold mb-2 text-cyan-400">Agent Execution Log</h3>
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
          </div>
        )}

        {output && (
          <WorkflowResults
            results={JSON.parse(output).workflow_results}
            artifacts={JSON.parse(output).artifacts}
          />
        )}
      </div>

      {showSpecModal && (
        <SpecInputModal
          onClose={() => setShowSpecModal(false)}
          onSubmit={(t, f) => executeWorkflow({ spec: t, file: f })}
        />
      )}
      {showCreateAgentModal && (
        <CreateAgentModal
          onClose={() => setShowCreateAgentModal(false)}
          onSubmit={(agent) => setCustomAgents((prev) => [...prev, agent])}
        />
      )}
    </div>
  );
}
