
"use client";

import React from "react";
import { Handle, Position } from "reactflow";

export default function AgentNode({
  data,
}: {
  data: { uiLabel: string; backendLabel: string; desc?: string };
}) {
  const handleSuggestNext = async () => {
    try {
      const domain =
        data?.backendLabel?.split(" ")[0]?.toLowerCase() || "system";
      const outputs = [data?.backendLabel || ""];

      const res = await fetch(`${API_BASE}/suggest_next_agent`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ outputs, domain }),
      });

      const j = await res.json();
      alert(
        `✨ Suggested Next Agent: ${
          j?.suggestion || j?.data || "No suggestion available"
        }`
      );
    } catch (e) {
      console.error("❌ AI suggestion error:", e);
      alert("Error contacting AI engine for next agent suggestion.");
    }
  };

  // ✅ NEW: When clicking the node → tell WorkflowConsole which agent to focus on
  const handleSelectAgent = () => {
    window.dispatchEvent(
      new CustomEvent("selectAgent", { detail: data.backendLabel })
    );
  };

  return (
    <div
      onClick={handleSelectAgent}   
      className="rounded-xl border border-cyan-400 bg-slate-800/90 text-white shadow-lg px-4 py-3 min-w-[220px] relative cursor-pointer hover:border-cyan-300 transition"
    >
      {/* Agent name */}
      <div className="font-bold text-cyan-300">
        {data?.uiLabel || "Agent"}
      </div>

      {/* Description */}
      {data?.desc && (
        <div className="mt-1 text-xs text-slate-300">{data.desc}</div>
      )}

      {/* Backend label */}
      <div className="mt-1 text-[10px] text-slate-500">
        {data?.backendLabel}
      </div>

      {/* ✨ AI Suggest Next */}
      <button
        onClick={(e) => {
          e.stopPropagation(); // prevent interfering with click-select behavior
          handleSuggestNext();
        }}
        className="absolute bottom-1 right-2 text-[10px] text-cyan-400 hover:text-cyan-300 transition-colors"
        title="AI Suggest Next Agent"
      >
        ✨ Suggest Next
      </button>

      {/* Handles for ReactFlow */}
      <Handle
        type="target"
        position={Position.Left}
        className="!bg-cyan-400"
      />
      <Handle
        type="source"
        position={Position.Right}
        className="!bg-cyan-400"
      />
    </div>
  );
}



