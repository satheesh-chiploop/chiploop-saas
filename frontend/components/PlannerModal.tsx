"use client";
import { useState } from "react";

export default function PlannerModal({ onClose }) {
  const [goal, setGoal] = useState("");
  const [plan, setPlan] = useState<any | null>(null);
  const [loading, setLoading] = useState(false);
  const [autoLoading, setAutoLoading] = useState(false);

  const handlePlan = async () => {
    setLoading(true);
    setPlan(null);
    try {
      const res = await fetch("/api/plan_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ prompt: goal }),
      });
      const data = await res.json();
      setPlan(data.plan || data);
    } catch (err) {
      alert("⚠️ Failed to generate workflow plan");
    } finally {
      setLoading(false);
    }
  };

  const handleAutoCompose = async () => {
    setAutoLoading(true);
    setPlan(null);
    try {
      const res = await fetch("/api/auto_compose_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ goal }),
      });
      const data = await res.json();
      if (data.status === "ok" || data.nodes) {
        setPlan({
          summary: data.summary,
          nodes: data.nodes,
          edges: data.edges,
        });
        alert(`✅ Auto-composed workflow:\n${data.summary}`);
      } else {
        alert(`⚠️ ${data.message || "Auto-compose failed."}`);
      }
    } catch (err) {
      alert("❌ Could not connect to backend");
    } finally {
      setAutoLoading(false);
    }
  };

  return (
    <div className="fixed inset-0 bg-black/70 flex items-center justify-center z-50">
      <div className="bg-slate-800 rounded-xl p-6 w-[600px] shadow-xl text-white">
        <h2 className="text-cyan-400 font-bold text-lg mb-3">
          🧠 AI Workflow Planner
        </h2>

        <textarea
          value={goal}
          onChange={(e) => setGoal(e.target.value)}
          placeholder="Describe your design goal..."
          className="w-full h-24 p-2 bg-slate-900 rounded border border-slate-700 text-sm text-slate-200 focus:ring-1 focus:ring-cyan-500"
        />

        <div className="mt-3 flex gap-2">
          <button
            onClick={handlePlan}
            disabled={loading || !goal.trim()}
            className="bg-cyan-700 hover:bg-cyan-600 px-3 py-1 rounded disabled:opacity-50"
          >
            {loading ? "Generating..." : "Generate Plan"}
          </button>

          <button
            onClick={handleAutoCompose}
            disabled={autoLoading || !goal.trim()}
            className="bg-cyan-700 hover:bg-cyan-600 px-3 py-1 rounded disabled:opacity-50"
          >
            {autoLoading ? "Composing..." : "🧠 Auto-Compose Flow"}
          </button>

          <button
            onClick={onClose}
            className="bg-slate-700 hover:bg-slate-600 px-3 py-1 rounded ml-auto"
          >
            Close
          </button>
        </div>

        {plan && (
          <div className="mt-4 bg-slate-900 rounded p-3 font-mono text-xs text-slate-200 overflow-auto max-h-64">
            <pre>{JSON.stringify(plan, null, 2)}</pre>
          </div>
        )}
      </div>
    </div>
  );
}
