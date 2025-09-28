
"use client";

import { Handle, Position } from "reactflow";

type AgentNodeProps = {
  data: { label: string; desc?: string };
};

export default function AgentNode({ data }: AgentNodeProps) {
  return (
    <div className="w-56 h-28 p-3 rounded-xl shadow-lg bg-slate-800 border border-slate-600 flex flex-col justify-center items-center text-center">
      {/* Top connector (incoming edge) */}
      <Handle type="target" position={Position.Top} />

      {/* Agent title */}
      <h4 className="font-bold text-sm text-cyan-400">{data.label}</h4>

      {/* Agent description */}
      {data.desc && <p className="text-xs text-slate-300 mt-2">{data.desc}</p>}

      {/* Bottom connector (outgoing edge) */}
      <Handle type="source" position={Position.Bottom} />
    </div>
  );
}

