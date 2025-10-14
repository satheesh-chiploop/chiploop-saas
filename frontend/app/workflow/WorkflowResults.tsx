"use client";

import React from "react";

type AgentResult = {
  label: string;
  status: string;
  artifact?: string;
  artifact_log?: string;
  log?: string;
  code?: string;
};

type Props = {
  results: Record<string, unknown>;
  artifacts: Record<string, Record<string, string>>;
};

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

export default function WorkflowResults({ results, artifacts }: Props) {
  if (!results || Object.keys(results).length === 0) {
    return <p className="mt-2 text-xs text-slate-400">No results available.</p>;
    // Prior version already returned a simple "No results available." line. :contentReference[oaicite:3]{index=3}
  }

  const parsed: AgentResult[] = Object.keys(results).map((label) => {
    const msg = results[label];
    const art = artifacts?.[label] || {};
    return {
      label,
      status: String(msg ?? ""),
      artifact: art.artifact ? String(art.artifact) : undefined,
      artifact_log: art.artifact_log ? String(art.artifact_log) : undefined,
      log: art.log ? String(art.log) : "",
      code: art.code ? String(art.code) : "",
    };
  });

  return (
    <div className="mt-3 space-y-3 text-xs">
      {parsed.map((agent) => (
        <div
          key={agent.label}
          className="rounded border border-slate-700 bg-slate-900/80 p-3 text-slate-200 shadow"
        >
          <h3 className="mb-1 font-bold text-cyan-400">{agent.label}</h3>
          <p className="mb-2 text-slate-300">
            Status: <span className="font-semibold">{agent.status}</span>
          </p>

          {agent.artifact && (
            <p className="mt-1 text-cyan-400">
              ➤ Output:{" "}
              <a
                href={`${API_BASE}${agent.artifact}`}
                target="_blank"
                rel="noopener noreferrer"
                className="underline hover:text-cyan-300"
              >
                {agent.artifact}
              </a>
            </p>
          )}

          {agent.artifact_log && (
            <p className="mt-1 text-cyan-400">
              ➤ Log:{" "}
              <a
                href={`${API_BASE}${agent.artifact_log}`}
                target="_blank"
                rel="noopener noreferrer"
                className="underline hover:text-cyan-300"
              >
                {agent.artifact_log}
              </a>
            </p>
          )}

          {agent.log && (
            <pre className="mt-2 max-h-56 overflow-auto rounded bg-black/70 p-2 text-[11px] leading-5 text-slate-200">
              {agent.log}
            </pre>
          )}

          {agent.code && (
            <pre className="mt-2 max-h-56 overflow-auto rounded bg-black/70 p-2 text-[11px] leading-5 text-slate-200">
              {agent.code}
            </pre>
          )}
        </div>
      ))}
    </div>
  );
}
