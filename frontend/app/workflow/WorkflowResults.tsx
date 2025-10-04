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
    return <p className="text-xs text-gray-400">No results available.</p>;
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
    <div className="space-y-3 text-xs mt-2">
      {parsed.map((agent) => (
        <div key={agent.label} className="border rounded p-2 bg-gray-800 text-gray-200">
          <h3 className="font-bold">{agent.label}</h3>
          <p>Status: {agent.status}</p>

          {agent.artifact && (
            <p className="text-cyan-400 mt-1">
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
            <p className="text-cyan-400 mt-1">
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
            <pre className="bg-gray-900 p-2 rounded mt-2 overflow-x-auto">{agent.log}</pre>
          )}

          {agent.code && (
            <pre className="bg-gray-900 p-2 rounded mt-2 overflow-x-auto">{agent.code}</pre>
          )}
        </div>
      ))}
    </div>
  );
}
