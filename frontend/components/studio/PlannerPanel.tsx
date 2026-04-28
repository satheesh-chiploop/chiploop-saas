"use client";

import { useMemo, useState } from "react";
import { ApiClientError, apiPost } from "@/lib/apiClient";

type ExistingAgentMatch = {
  name: string;
  score: number;
  match_reasons?: string[];
  loop_type?: string;
  domain?: string;
  entrypoint?: string;
};

type AgentPlanResult = {
  requested_capability: string;
  exact_matches: ExistingAgentMatch[];
  similar_matches: ExistingAgentMatch[];
  reusable_skills: string[];
  reusable_tools: string[];
  reusable_hooks: string[];
  missing_capabilities: string[];
  recommendation: string;
  confidence_score: number;
  explanation: string;
};

type PlannerResponse = {
  status: string;
  result: AgentPlanResult;
};

type PlannerPanelProps = {
  loopType: string;
  onUseAgent?: (agentName: string) => void;
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Planner request failed.";
}

function MatchList({
  title,
  matches,
  onUseAgent,
}: {
  title: string;
  matches: ExistingAgentMatch[];
  onUseAgent?: (agentName: string) => void;
}) {
  return (
    <section>
      <h4 className="mb-2 text-sm font-bold text-cyan-300">{title}</h4>
      {matches.length === 0 ? (
        <div className="rounded-lg border border-slate-800 bg-black/20 p-3 text-xs text-slate-500">
          None found.
        </div>
      ) : (
        <div className="space-y-2">
          {matches.map((match) => (
            <div
              key={`${title}-${match.name}`}
              className="rounded-lg border border-slate-800 bg-black/30 p-3"
            >
              <div className="flex items-start justify-between gap-3">
                <div className="min-w-0">
                  <div className="truncate text-sm font-semibold text-slate-100">
                    {match.name}
                  </div>
                  <div className="mt-1 text-xs text-slate-400">
                    Score: {Math.round((match.score || 0) * 100)}%
                    {match.domain ? ` | ${match.domain}` : ""}
                    {match.loop_type ? ` | ${match.loop_type}` : ""}
                  </div>
                </div>
                {onUseAgent ? (
                  <button
                    onClick={() => onUseAgent(match.name)}
                    className="shrink-0 rounded-md border border-cyan-700 px-2 py-1 text-xs text-cyan-200 hover:bg-cyan-950/50"
                  >
                    Use
                  </button>
                ) : null}
              </div>
              {match.match_reasons?.length ? (
                <div className="mt-2 flex flex-wrap gap-1">
                  {match.match_reasons.map((reason) => (
                    <span
                      key={`${match.name}-${reason}`}
                      className="rounded-full border border-slate-700 px-2 py-0.5 text-[11px] text-slate-300"
                    >
                      {reason}
                    </span>
                  ))}
                </div>
              ) : null}
            </div>
          ))}
        </div>
      )}
    </section>
  );
}

function ChipList({ title, items }: { title: string; items: string[] }) {
  return (
    <div>
      <div className="mb-2 text-xs font-semibold uppercase text-slate-400">{title}</div>
      {items.length === 0 ? (
        <div className="text-xs text-slate-500">None</div>
      ) : (
        <div className="flex flex-wrap gap-1.5">
          {items.map((item) => (
            <span
              key={`${title}-${item}`}
              className="rounded-full border border-slate-700 bg-slate-950 px-2 py-1 text-[11px] text-slate-200"
            >
              {item}
            </span>
          ))}
        </div>
      )}
    </div>
  );
}

export default function PlannerPanel({ loopType, onUseAgent }: PlannerPanelProps) {
  const [requestText, setRequestText] = useState("");
  const [domain, setDomain] = useState("");
  const [result, setResult] = useState<AgentPlanResult | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const canSubmit = useMemo(() => requestText.trim().length > 0 && !loading, [requestText, loading]);

  async function runPlanner() {
    if (!canSubmit) return;
    setLoading(true);
    setError(null);
    try {
      const response = await apiPost<PlannerResponse>("/studio/agent-planner/plan", {
        natural_language_request: requestText.trim(),
        loop_type: loopType,
        domain: domain.trim() || undefined,
      });
      setResult(response.result);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  return (
    <div className="flex min-h-0 flex-col rounded-xl border border-slate-800 bg-black/30">
      <div className="border-b border-slate-800 p-4">
        <div className="flex items-center justify-between gap-3">
          <div>
            <h3 className="text-lg font-bold text-cyan-400">Planner</h3>
            <p className="mt-1 text-xs text-slate-400">
              Find reusable agents before creating anything new.
            </p>
          </div>
          <span className="rounded-full border border-slate-700 px-2 py-1 text-[11px] text-slate-400">
            {loopType}
          </span>
        </div>

        <textarea
          value={requestText}
          onChange={(event) => setRequestText(event.target.value)}
          className="mt-4 h-24 w-full resize-none rounded-lg border border-slate-700 bg-slate-950/70 p-3 text-sm text-slate-100 outline-none focus:border-cyan-600"
          placeholder="Describe the capability you need..."
        />

        <div className="mt-3 flex gap-2">
          <input
            value={domain}
            onChange={(event) => setDomain(event.target.value)}
            className="min-w-0 flex-1 rounded-lg border border-slate-700 bg-slate-950/70 px-3 py-2 text-sm text-slate-100 outline-none focus:border-cyan-600"
            placeholder="Optional domain"
          />
          <button
            onClick={runPlanner}
            disabled={!canSubmit}
            className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
          >
            {loading ? "Planning..." : "Plan"}
          </button>
        </div>
      </div>

      <div className="min-h-0 flex-1 space-y-4 overflow-y-auto p-4 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
        {error ? (
          <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
            {error}
          </div>
        ) : null}

        {!result && !error ? (
          <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-400">
            Enter a requirement and run the planner. This does not modify workflows,
            registries, or generated files.
          </div>
        ) : null}

        {result ? (
          <>
            <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-3">
              <div className="flex items-center justify-between gap-3">
                <div>
                  <div className="text-xs uppercase text-slate-500">Recommendation</div>
                  <div className="mt-1 text-sm font-semibold text-slate-100">
                    {result.recommendation}
                  </div>
                </div>
                <div className="text-right">
                  <div className="text-xs uppercase text-slate-500">Confidence</div>
                  <div className="mt-1 text-lg font-bold text-cyan-300">
                    {Math.round((result.confidence_score || 0) * 100)}%
                  </div>
                </div>
              </div>
              {result.explanation ? (
                <p className="mt-3 text-xs leading-5 text-slate-300">{result.explanation}</p>
              ) : null}
            </section>

            <MatchList title="Exact Matches" matches={result.exact_matches || []} onUseAgent={onUseAgent} />
            <MatchList title="Similar Matches" matches={result.similar_matches || []} />

            <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-3">
              <h4 className="mb-3 text-sm font-bold text-cyan-300">Reusable Components</h4>
              <div className="space-y-3">
                <ChipList title="Skills" items={result.reusable_skills || []} />
                <ChipList title="Tools" items={result.reusable_tools || []} />
                <ChipList title="Hooks" items={result.reusable_hooks || []} />
              </div>
            </section>

            <section>
              <h4 className="mb-2 text-sm font-bold text-cyan-300">Missing Capabilities</h4>
              {(result.missing_capabilities || []).length === 0 ? (
                <div className="rounded-lg border border-slate-800 bg-black/20 p-3 text-xs text-slate-500">
                  None reported.
                </div>
              ) : (
                <div className="space-y-1">
                  {result.missing_capabilities.map((item) => (
                    <div
                      key={item}
                      className="rounded-lg border border-slate-800 bg-black/20 p-2 text-xs text-slate-300"
                    >
                      {item}
                    </div>
                  ))}
                </div>
              )}
            </section>

            <button
              type="button"
              onClick={() => alert("Agent Factory dry-run UI is planned for Phase 7D.")}
              className="w-full rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
            >
              Generate Agent (dry-run)
            </button>
          </>
        ) : null}
      </div>
    </div>
  );
}
