
"use client";

import React from "react";
import { Handle, Position } from "reactflow";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

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
      className="relative w-[264px] cursor-pointer rounded-lg border border-cyan-400 bg-slate-800/90 px-4 py-3 text-white shadow-lg transition hover:border-cyan-300"
    >
      {/* Agent name */}
      <div className="break-words pr-2 text-sm font-bold leading-5 text-cyan-300">
        {data?.uiLabel || "Agent"}
      </div>

      {/* Description */}
      {data?.desc && (
        <div className="mt-2 line-clamp-3 break-words text-xs leading-5 text-slate-300">{data.desc}</div>
      )}

      {/* Backend label */}
      <div className="mt-2 break-words pr-16 text-[10px] leading-4 text-slate-400">
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
      <span className="pointer-events-none absolute -left-3 top-1/2 z-10 -translate-x-full -translate-y-1/2 rounded bg-slate-950 px-1.5 py-0.5 text-[9px] font-bold text-emerald-300">
        IN
      </span>
      <Handle
        type="target"
        position={Position.Left}
        className="!-left-2.5 !h-5 !w-5 !border-2 !border-slate-950 !bg-emerald-400"
      />
      <span className="pointer-events-none absolute -right-3 top-1/2 z-10 translate-x-full -translate-y-1/2 rounded bg-slate-950 px-1.5 py-0.5 text-[9px] font-bold text-cyan-300">
        OUT
      </span>
      <Handle
        type="source"
        position={Position.Right}
        className="!-right-2.5 !h-5 !w-5 !border-2 !border-slate-950 !bg-cyan-400"
      />
    </div>
  );
}



