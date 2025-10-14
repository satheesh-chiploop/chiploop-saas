"use client";

import React from "react";
import { Handle, Position } from "reactflow";

export default function AgentNode({
  data,
}: {
  data: { uiLabel: string; backendLabel: string; desc?: string };
}) {
  return (
    <div className="rounded-xl border border-cyan-400 bg-slate-800/90 text-white shadow-lg px-4 py-3 min-w-[220px]">
      <div className="font-bold text-cyan-300">{data?.uiLabel || "Agent"}</div>
      {data?.desc && <div className="mt-1 text-xs text-slate-300">{data.desc}</div>}
      {/* show backend label for transparency */}
      <div className="mt-1 text-[10px] text-slate-500">{data?.backendLabel}</div>

      <Handle type="target" position={Position.Left} className="!bg-cyan-400" />
      <Handle type="source" position={Position.Right} className="!bg-cyan-400" />
    </div>
  );
}
