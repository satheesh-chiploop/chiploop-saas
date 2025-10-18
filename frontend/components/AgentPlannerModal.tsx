"use client";
import { useState } from "react";

export default function AgentPlannerModal({ onClose }) {
  const [goal, setGoal] = useState("");
  const [agent, setAgent] = useState<any | null>(null);
  const [loading, setLoading] = useState(false);
  const [tab, setTab] = useState<"spec" | "code">("spec");
  const [backendSource, setBackendSource] = useState<string>("");

  const handlePlan = async () => {
    setLoading(true);
    setAgent(null);
    setBackendSource("");

    try {
      const res = await fetch("/api/plan_agent", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ prompt: goal }),
      });
      const data = await res.json();

      if (data?.agent) {
        setAgent(data.agent);
        const text = JSON.stringify(data.agent).toLowerCase();
        if (text.includes("ollama")) setBackendSource("🦙 Local Ollama");
        else if (text.includes("portkey")) setBackendSource("🪄 Portkey");
        else if (text.includes("openai")) setBackendSource("🌐 OpenAI");
        else setBackendSource("⚠️ Static Fallback");
      } else setBackendSource("⚠️ Unknown");
    } catch (e) {
      console.error(e);
      setBackendSource("❌ Request Failed");
    } finally {
      setLoading(false);
    }
  };

  const handleSave = async () => {
    if (!agent) return;
    try {
      const res = await fetch("/api/save_custom_agent", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ agent }),
      });
      const data = await res.json();
      if (data.status === "ok") {
        window.dispatchEvent(new CustomEvent("customAgentSaved"));
        alert(`✅ Agent "${agent.agent_name}" saved to Custom Agents`);
      } else {
        alert(`❌ Save failed: ${data.message}`);
      }
    } catch (e) {
      alert("⚠️ Could not connect to backend");
    }
  };

  return (
    <div className="fixed inset-0 bg-black/70 flex justify-end z-50">
      <div className="bg-slate-800 w-[520px] h-full p-6 overflow-y-auto border-l border-slate-700 text-white shadow-xl">
        {/* Header */}
        <div className="flex items-center justify-between mb-3">
          <h2 className="text-purple-400 font-bold text-lg">🧬 AI Agent Planner</h2>
          <button
            onClick={onClose}
            className="text-slate-400 hover:text-white text-xl leading-none"
          >
            ✕
          </button>
        </div>

        {/* Input area */}
        <textarea
          value={goal}
          onChange={(e) => setGoal(e.target.value)}
          placeholder="Describe the agent you want to create..."
          className="w-full h-28 p-2 bg-slate-900 rounded border border-slate-700 text-sm text-slate-200 focus:ring-1 focus:ring-purple-500"
        />

        <div className="mt-3 flex gap-2">
          <button
            onClick={handlePlan}
            disabled={loading || !goal.trim()}
            className="bg-purple-700 hover:bg-purple-600 px-3 py-1 rounded disabled:opacity-50"
          >
            {loading ? "Generating..." : "Generate Agent"}
          </button>
          <button
            onClick={onClose}
            className="bg-slate-700 hover:bg-slate-600 px-3 py-1 rounded"
          >
            Close
          </button>
          {agent?.agent_name && (
            <button
              onClick={handleSave}
              className="bg-green-700 hover:bg-green-600 px-3 py-1 rounded text-xs ml-auto"
            >
              💾 Save to Custom Agents
            </button>
          )}
        </div>

        {/* Status + Backend Source */}
        {backendSource && (
          <div className="mt-3 text-xs text-slate-400">
            <span className="font-semibold text-slate-300">Backend: </span>
            {backendSource}
          </div>
        )}

        {/* Output */}
        {agent && (
          <div className="mt-5">
            <div className="flex gap-3 mb-2 text-sm">
              <button
                className={`px-3 py-1 rounded ${
                  tab === "spec" ? "bg-purple-700" : "bg-slate-700"
                }`}
                onClick={() => setTab("spec")}
              >
                Spec
              </button>
              <button
                className={`px-3 py-1 rounded ${
                  tab === "code" ? "bg-purple-700" : "bg-slate-700"
                }`}
                onClick={() => setTab("code")}
              >
                Code
              </button>
            </div>

            {tab === "spec" && (
              <pre className="bg-slate-900 rounded p-3 text-xs overflow-auto max-h-80 text-slate-200">
                {JSON.stringify(
                  {
                    agent_name: agent.agent_name,
                    domain: agent.domain,
                    inputs: agent.inputs,
                    outputs: agent.outputs,
                    description: agent.description,
                  },
                  null,
                  2
                )}
              </pre>
            )}

            {tab === "code" && (
              <div className="bg-slate-900 rounded p-3 text-xs text-slate-400 italic">
                Code generation is disabled in this version.
              </div>
            )}
          </div>
        )}
      </div>
    </div>
  );
}
