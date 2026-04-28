"use client";

import { useMemo, useState } from "react";
import { ApiClientError, apiPost } from "@/lib/apiClient";
import AgentFactoryDryRunModal from "./AgentFactoryDryRunModal";
import type { GeneratedAgentReviewItem } from "./GeneratedAgentReviewModal";

const LOOP_OPTIONS = ["digital", "analog", "embedded", "system", "validation"];

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

type SavedPlan = {
  name: string;
  loopType: string;
  result: AgentPlanResult;
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Planner request failed.";
}

function MatchList({ title, matches }: { title: string; matches: ExistingAgentMatch[] }) {
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
            <div key={`${title}-${match.name}`} className="rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="min-w-0">
                <div className="truncate text-sm font-semibold text-slate-100">{match.name}</div>
                <div className="mt-1 text-xs text-slate-400">
                  Score: {Math.round((match.score || 0) * 100)}%
                  {match.domain ? ` | ${match.domain}` : ""}
                  {match.loop_type ? ` | ${match.loop_type}` : ""}
                </div>
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

export default function StudioAgentPlannerModal({
  initialLoop,
  onFactoryDryRunResult,
  onClose,
}: {
  initialLoop: string;
  onFactoryDryRunResult?: (item: GeneratedAgentReviewItem) => void;
  onClose: () => void;
}) {
  const [requestText, setRequestText] = useState("");
  const [loopType, setLoopType] = useState(initialLoop || "digital");
  const [domain, setDomain] = useState("");
  const [name, setName] = useState("");
  const [result, setResult] = useState<AgentPlanResult | null>(null);
  const [savedPlans, setSavedPlans] = useState<SavedPlan[]>([]);
  const [showFactoryDryRun, setShowFactoryDryRun] = useState(false);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [savedMessage, setSavedMessage] = useState<string | null>(null);

  const canSubmit = useMemo(() => requestText.trim().length > 0 && !loading, [requestText, loading]);
  const canSave = Boolean(result);
  const canOpenFactory = Boolean(
    result &&
      ["create_new", "extend_existing", "extend_or_create_variant"].includes(result.recommendation)
  );

  async function runPlanner() {
    if (!canSubmit) return;
    setLoading(true);
    setError(null);
    setSavedMessage(null);
    try {
      const response = await apiPost<PlannerResponse>("/studio/agent-planner/plan", {
        natural_language_request: requestText.trim(),
        loop_type: loopType,
        domain: domain.trim() || undefined,
        name: name.trim() || undefined,
      });
      setResult(response.result);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  function savePlan() {
    if (!result) return;
    const plannedName = name.trim() || result.exact_matches?.[0]?.name || "Untitled planned agent";
    setSavedPlans((current) => current.concat({ name: plannedName, loopType, result }));
    setSavedMessage(`Saved "${plannedName}" locally for this Studio session.`);
  }

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex max-h-[88vh] w-full max-w-5xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Agent Planner</h2>
            <p className="mt-1 text-sm text-slate-400">
              Find reusable agents before creating anything new.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="grid min-h-0 flex-1 grid-cols-1 gap-0 md:grid-cols-[360px_1fr]">
          <section className="border-b border-slate-800 p-5 md:border-b-0 md:border-r">
            <label className="block text-sm font-semibold text-slate-200">Planned agent name</label>
            <input
              value={name}
              onChange={(event) => setName(event.target.value)}
              className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600"
              placeholder="Optional name"
            />

            <label className="mt-4 block text-sm font-semibold text-slate-200">Loop</label>
            <select
              value={loopType}
              onChange={(event) => setLoopType(event.target.value)}
              className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600"
            >
              {LOOP_OPTIONS.map((option) => (
                <option key={option} value={option}>
                  {option[0].toUpperCase() + option.slice(1)}
                </option>
              ))}
            </select>

            <label className="mt-4 block text-sm font-semibold text-slate-200">Domain</label>
            <input
              value={domain}
              onChange={(event) => setDomain(event.target.value)}
              className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600"
              placeholder="Optional domain"
            />

            <label className="mt-4 block text-sm font-semibold text-slate-200">Requirement</label>
            <textarea
              value={requestText}
              onChange={(event) => setRequestText(event.target.value)}
              className="mt-2 h-40 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 text-sm outline-none focus:border-cyan-600"
              placeholder="Describe the capability you need..."
            />

            <div className="mt-4 flex gap-2">
              <button
                onClick={runPlanner}
                disabled={!canSubmit}
                className="flex-1 rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
              >
                {loading ? "Running..." : "Run"}
              </button>
              <button
                onClick={savePlan}
                disabled={!canSave}
                className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
              >
                Save
              </button>
            </div>

            {savedPlans.length ? (
              <div className="mt-4 rounded-lg border border-slate-800 bg-black/30 p-3 text-xs text-slate-300">
                Saved locally: {savedPlans.length}
              </div>
            ) : null}
          </section>

          <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            {error ? (
              <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
                {error}
              </div>
            ) : null}
            {savedMessage ? (
              <div className="mb-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
                {savedMessage}
              </div>
            ) : null}

            {!result && !error ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
                Run the planner to see matching agents, reusable components, and missing capabilities.
              </div>
            ) : null}

            {result ? (
              <div className="space-y-4">
                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
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

                <MatchList title="Exact Matches" matches={result.exact_matches || []} />
                <MatchList title="Similar Matches" matches={result.similar_matches || []} />

                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
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
                        <div key={item} className="rounded-lg border border-slate-800 bg-black/20 p-2 text-xs text-slate-300">
                          {item}
                        </div>
                      ))}
                    </div>
                  )}
                </section>

                {canOpenFactory ? (
                  <button
                    type="button"
                    onClick={() => setShowFactoryDryRun(true)}
                    className="w-full rounded-lg border border-cyan-700 bg-cyan-950/30 px-3 py-2 text-sm font-semibold text-cyan-100 hover:bg-cyan-900/40"
                  >
                    Generate Agent Dry Run
                  </button>
                ) : null}
              </div>
            ) : null}
          </section>
        </div>
      </div>
      {showFactoryDryRun && result ? (
        <AgentFactoryDryRunModal
          initialRequest={{
            name: name.trim() || result.missing_capabilities?.[0] || "Planned Agent",
            natural_language_request: requestText.trim() || result.requested_capability,
            loop_type: loopType,
            domain: domain.trim() || undefined,
            inputs: [],
            outputs: result.missing_capabilities || [],
            required_skills: result.reusable_skills || [],
            required_tools: result.reusable_tools || [],
            required_hooks: result.reusable_hooks || [],
            allow_extension: result.recommendation !== "create_new",
          }}
          onDryRunResult={onFactoryDryRunResult}
          onClose={() => setShowFactoryDryRun(false)}
        />
      ) : null}
    </div>
  );
}
