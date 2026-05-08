"use client";

import { FormEvent, useState } from "react";
import { apiPost } from "@/lib/apiClient";

type AskThisRunResponse = {
  workflow_id: string;
  question: string;
  answer: string;
  sources?: Array<{ type: string; path: string }>;
  source_count?: number;
};

type Props = {
  workflowId: string | null | undefined;
  compact?: boolean;
};

const suggestions = [
  "Summarize this run and the key artifacts.",
  "What should I inspect first?",
  "Are there warnings, failures, or missing outputs?",
  "What is the recommended next step?",
];

export default function AskThisRunPanel({ workflowId, compact = false }: Props) {
  const [question, setQuestion] = useState("");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [history, setHistory] = useState<AskThisRunResponse[]>([]);

  async function ask(questionOverride?: string) {
    const text = (questionOverride || question).trim();
    if (!workflowId || !text || loading) return;
    setLoading(true);
    setError(null);
    try {
      const response = await apiPost<AskThisRunResponse>(`/workflow/${workflowId}/ask`, { question: text });
      setHistory((current) => [response, ...current].slice(0, 10));
      setQuestion("");
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "Ask This Run failed.");
    } finally {
      setLoading(false);
    }
  }

  function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    ask();
  }

  if (!workflowId) return null;

  return (
    <div className={`rounded-xl border border-cyan-900/60 bg-cyan-950/20 ${compact ? "p-4" : "p-5"}`}>
      <div className="font-semibold text-cyan-200">Ask This Run</div>
      <p className="mt-1 text-sm leading-6 text-cyan-100/80">
        Ask questions about this run&apos;s logs, generated files, reports, warnings, and next steps.
      </p>

      <div className="mt-3 flex flex-wrap gap-2">
        {suggestions.map((suggestion) => (
          <button
            key={suggestion}
            type="button"
            disabled={loading}
            onClick={() => ask(suggestion)}
            className="rounded border border-cyan-700 px-3 py-1 text-xs text-cyan-100 hover:bg-cyan-900/40 disabled:cursor-not-allowed disabled:opacity-50"
          >
            {suggestion}
          </button>
        ))}
      </div>

      <form onSubmit={submit} className="mt-3 space-y-3">
        <textarea
          value={question}
          onChange={(event) => setQuestion(event.target.value)}
          placeholder="Ask about failures, warnings, generated files, coverage, handoff readiness..."
          className="min-h-20 w-full rounded-lg border border-slate-700 bg-slate-950 p-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
        />
        <button
          type="submit"
          disabled={loading || question.trim().length < 3}
          className="rounded bg-cyan-700 px-4 py-2 text-sm font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
        >
          {loading ? "Inspecting..." : "Ask this run"}
        </button>
      </form>

      {error ? (
        <div className="mt-3 rounded border border-red-800 bg-red-950/40 p-3 text-sm text-red-200">{error}</div>
      ) : null}

      <div className="mt-4 space-y-3">
        {history.map((item, index) => (
          <div key={`${item.question}-${index}`} className="rounded-lg border border-slate-700 bg-slate-900/50 p-4">
            <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Question</div>
            <div className="mt-1 text-slate-100">{item.question}</div>
            <div className="mt-4 text-xs font-semibold uppercase tracking-wide text-cyan-300">Answer</div>
            <div className="mt-2 whitespace-pre-wrap leading-6 text-slate-200">{item.answer}</div>
            {item.sources?.length ? (
              <div className="mt-4">
                <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Sources</div>
                <div className="mt-2 flex flex-wrap gap-2">
                  {item.sources.slice(0, 8).map((source) => (
                    <span key={`${source.type}-${source.path}`} className="rounded bg-slate-800 px-2 py-1 text-xs text-slate-300">
                      {source.path}
                    </span>
                  ))}
                </div>
              </div>
            ) : null}
          </div>
        ))}
      </div>
    </div>
  );
}
