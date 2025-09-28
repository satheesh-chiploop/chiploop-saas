"use client";
import { useState } from "react";

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
  state: Record<string, unknown>;
};

export default function WorkflowResults({ results, state }: Props) {
  const [expanded, setExpanded] = useState<string | null>(null);

  const parseResults = (): AgentResult[] => {
    return Object.keys(results).map((label) => {
      const msg = results[label];

      let artifact: string | undefined;
      let artifact_log: string | undefined;

      if (label === "📘 Spec Agent") {
        artifact = state?.rtl ? "backend/design.v" : undefined;
        artifact_log = "spec_agent_compile.log";
      } else if (label === "💻 RTL Agent") {
        artifact = state?.rtl ? "backend/design.v" : undefined;
        artifact_log = "rtl_agent_compile.log";
      } else {
        artifact_log = state?.artifact_log ? state.artifact_log : undefined;
      }
     return {
       label,
      status: String(msg ?? ""),                             // ensure string
      artifact,
      artifact_log,
      log: String(state?.error_log ?? state?.lint_log ?? ""), // ensure string
      code: state?.rtl ? String(state.rtl) : "",             // ensure string
     };
 
    });
  };

  const data = parseResults();

  return (
    <div className="absolute bottom-0 left-0 right-0 max-h-72 overflow-y-auto bg-slate-900/95 border-t border-slate-700 p-4 text-sm text-slate-200">
      <h3 className="text-lg font-bold mb-3">Workflow Results</h3>
      <div className="space-y-3">
        {data.map((agent) => (
          <div
            key={agent.label}
            className="p-3 rounded-lg bg-slate-800 shadow border border-slate-700"
          >
            <div className="flex justify-between items-center">
              <span className="font-semibold">{agent.label}</span>
              <span>
                {agent.status.startsWith("✅") && "✅"}
                {agent.status.startsWith("❌") && "❌"}
                {agent.status.startsWith("⚠") && "⚠"}
              </span>
            </div>

            <p className="text-slate-300 mt-1">{agent.status}</p>

            {agent.artifact && (
              <p className="text-cyan-400 text-xs mt-1">
                ➤ Output:{" "}
                <a
                  href={`http://127.0.0.1:8000/artifact/${agent.artifact.split("/").pop()}`}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="underline hover:text-cyan-300"
                >
                  {agent.artifact}
                </a>
              </p>
            )}

            {agent.artifact_log && (
              <p className="text-cyan-400 text-xs mt-1">
                ➤ Log:{" "}
                <a
                  href={`http://127.0.0.1:8000/artifact/${agent.artifact_log}`}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="underline hover:text-cyan-300"
                >
                  {agent.artifact_log}
                </a>
              </p>
            )}

            {agent.log && (
              <button
                onClick={() =>
                  setExpanded(expanded === agent.label ? null : agent.label)
                }
                className="text-xs mt-2 text-indigo-400 underline"
              >
                {expanded === agent.label ? "Hide Details" : "View Details"}
              </button>
            )}

            {expanded === agent.label && (
              <pre className="mt-2 p-2 rounded bg-black text-green-300 text-xs overflow-x-auto max-h-40">
                {agent.log || agent.code}
              </pre>
            )}
          </div>
        ))}
      </div>
    </div>
  );
}
