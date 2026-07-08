"use client";

import React from "react";
import { Handle, Position } from "reactflow";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

export default function AgentNode({
  data,
}: {
  data: {
    uiLabel: string;
    backendLabel: string;
    desc?: string;
    nodeSize?: "regular" | "cozy" | "compact";
  };
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
        `Suggested next agent: ${
          j?.suggestion || j?.data || "No suggestion available"
        }`
      );
    } catch (e) {
      console.error("AI suggestion error:", e);
      alert("Error contacting AI engine for next agent suggestion.");
    }
  };

  const handleSelectAgent = () => {
    window.dispatchEvent(
      new CustomEvent("selectAgent", { detail: data.backendLabel })
    );
  };

  const nodeSize = data?.nodeSize || "regular";
  const sizeClasses = {
    regular: {
      card: "w-[236px] px-3 py-2.5",
      title: "text-[13px] leading-4",
      desc: "line-clamp-2 text-[11px] leading-4",
      backend: "pr-14 text-[10px] leading-3",
      action: "text-[10px]",
    },
    cozy: {
      card: "w-[220px] px-3 py-2",
      title: "text-[12px] leading-4",
      desc: "line-clamp-1 text-[10px] leading-3",
      backend: "pr-12 text-[9px] leading-3",
      action: "text-[9px]",
    },
    compact: {
      card: "w-[204px] px-2.5 py-2",
      title: "text-[11px] leading-3",
      desc: "line-clamp-1 text-[9px] leading-3",
      backend: "pr-10 text-[8px] leading-3",
      action: "text-[8px]",
    },
  }[nodeSize];

  return (
    <div
      onClick={handleSelectAgent}
      className={`relative cursor-pointer rounded-md border border-cyan-400 bg-slate-800/90 text-white shadow-lg transition hover:border-cyan-300 ${sizeClasses.card}`}
    >
      <div className={`break-words pr-2 font-bold text-cyan-300 ${sizeClasses.title}`}>
        {data?.uiLabel || "Agent"}
      </div>

      {data?.desc && (
        <div className={`mt-1.5 break-words text-slate-300 ${sizeClasses.desc}`}>
          {data.desc}
        </div>
      )}

      <div className={`mt-1.5 break-words text-slate-400 ${sizeClasses.backend}`}>
        {data?.backendLabel}
      </div>

      <button
        onClick={(e) => {
          e.stopPropagation();
          handleSuggestNext();
        }}
        className={`absolute bottom-1 right-2 text-cyan-400 transition-colors hover:text-cyan-300 ${sizeClasses.action}`}
        title="AI Suggest Next Agent"
      >
        Suggest Next
      </button>

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
