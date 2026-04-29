"use client";

import { useEffect, useMemo, useState } from "react";
import { ApiClientError, apiPost } from "@/lib/apiClient";

type ExistingAgentMatch = {
  name: string;
  score?: number;
  match_reasons?: string[];
  loop_type?: string;
  domain?: string;
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

type FactoryPlan = {
  decision?: string;
  proposed_agent_spec?: Record<string, unknown>;
  proposed_skill_specs?: Record<string, unknown>[];
  proposed_tool_refs?: string[];
  proposed_hook_refs?: string[];
  files_to_generate?: Array<{
    path?: string;
    description?: string;
    content_preview?: string;
  }>;
  registry_patch?: {
    path?: string;
    content?: string;
  } | null;
  validation_checklist?: string[];
  risk_notes?: string[];
};

type FactoryResult = {
  ok: boolean;
  dry_run: boolean;
  plan: FactoryPlan;
  errors?: string[];
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Missing agent resolver failed.";
}

function defaultAgentName(raw: string, loopType: string): string {
  const base = raw
    .replace(/[_-]+/g, " ")
    .trim()
    .split(" ")
    .filter(Boolean)
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
  const prefix = loopType ? loopType.charAt(0).toUpperCase() + loopType.slice(1) : "System";
  const withAgent = base.toLowerCase().endsWith("agent") ? base : `${base} Agent`;
  return withAgent.toLowerCase().startsWith(prefix.toLowerCase()) ? withAgent : `${prefix} ${withAgent}`;
}

function MatchCard({
  match,
  onUse,
}: {
  match: ExistingAgentMatch;
  onUse: (name: string) => void;
}) {
  return (
    <div className="rounded-lg border border-slate-800 bg-slate-950 p-3">
      <div className="flex items-start justify-between gap-3">
        <div>
          <div className="text-sm font-semibold text-slate-100">{match.name}</div>
          <div className="mt-1 text-xs text-slate-400">
            Score: {Math.round((match.score || 0) * 100)}%
            {match.loop_type ? ` | ${match.loop_type}` : ""}
          </div>
        </div>
        <button
          onClick={() => onUse(match.name)}
          className="shrink-0 rounded border border-emerald-700 bg-emerald-950/30 px-2 py-1 text-xs text-emerald-100 hover:bg-emerald-900/40"
        >
          Use
        </button>
      </div>
    </div>
  );
}

export default function MissingAgentsResolverModal({
  missingAgents,
  goal,
  loopType,
  domain,
  spec,
  baseAgents,
  onResolved,
  onClose,
}: {
  missingAgents: string[];
  goal: string;
  loopType: string;
  domain?: string;
  spec?: unknown;
  baseAgents: string[];
  onResolved: (resolvedAgents: string[]) => void;
  onClose: () => void;
}) {
  const [index, setIndex] = useState(0);
  const [resolvedAgents, setResolvedAgents] = useState<string[]>([]);
  const [plannedName, setPlannedName] = useState("");
  const [plannerResult, setPlannerResult] = useState<AgentPlanResult | null>(null);
  const [factoryResult, setFactoryResult] = useState<FactoryResult | null>(null);
  const [savedMessage, setSavedMessage] = useState<string | null>(null);
  const [loading, setLoading] = useState<"planner" | "factory" | "save" | null>(null);
  const [error, setError] = useState<string | null>(null);

  const currentMissing = missingAgents[index] || "";
  const complete = index >= missingAgents.length;
  const canCreate = Boolean(
    plannerResult &&
      ["create_new", "extend_existing", "extend_or_create_variant"].includes(plannerResult.recommendation)
  );

  const requestText = useMemo(() => {
    const specContext = spec ? `\n\nStructured spec context:\n${JSON.stringify(spec).slice(0, 1200)}` : "";
    return `Resolve missing ChipLoop agent capability: ${currentMissing}\n\nWorkflow goal:\n${goal}${specContext}`;
  }, [currentMissing, goal, spec]);

  useEffect(() => {
    if (!currentMissing) return;
    setPlannedName(defaultAgentName(currentMissing, loopType || "system"));
    setPlannerResult(null);
    setFactoryResult(null);
    setSavedMessage(null);
    setError(null);
  }, [currentMissing, loopType]);

  useEffect(() => {
    if (!currentMissing || complete) return;
    runPlanner();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [currentMissing]);

  async function runPlanner() {
    if (!currentMissing) return;
    setLoading("planner");
    setError(null);
    setFactoryResult(null);
    try {
      const response = await apiPost<{ status: string; result: AgentPlanResult }>("/studio/agent-planner/plan", {
        natural_language_request: requestText,
        loop_type: loopType,
        domain: domain || loopType,
        name: plannedName,
      });
      setPlannerResult(response.result);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  async function runFactoryDryRun() {
    setLoading("factory");
    setError(null);
    try {
      const response = await apiPost<{ status: string; result: FactoryResult }>("/studio/agent-factory/dry-run", {
        dry_run: true,
        request: {
          name: plannedName,
          natural_language_request: requestText,
          loop_type: loopType,
          domain: domain || loopType,
          inputs: [],
          outputs: plannerResult?.missing_capabilities || [currentMissing],
          required_skills: plannerResult?.reusable_skills || [],
          required_tools: plannerResult?.reusable_tools || [],
          required_hooks: plannerResult?.reusable_hooks || [],
          allow_extension: plannerResult?.recommendation !== "create_new",
        },
      });
      setFactoryResult(response.result);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  function resolveWith(agentName: string) {
    const next = resolvedAgents.concat(agentName);
    setResolvedAgents(next);
    if (next.length >= missingAgents.length) {
      onResolved(next);
      return;
    }
    setIndex(index + 1);
  }

  async function savePrivateAgent() {
    if (!factoryResult?.plan) return;
    setLoading("save");
    setError(null);
    try {
      const plan = factoryResult.plan;
      const spec = plan.proposed_agent_spec || {};
      const response = await apiPost<{ status: string; agent: { agent_name?: string } }>("/studio/user-agents", {
        name: plannedName,
        loop_type: loopType,
        domain: domain || loopType,
        description: String(spec.description || requestText),
        agent_spec: spec,
        skills: plan.proposed_skill_specs || plannerResult?.reusable_skills || [],
        tools: plan.proposed_tool_refs || plannerResult?.reusable_tools || [],
        hooks: plan.proposed_hook_refs || plannerResult?.reusable_hooks || [],
        generated_files: plan.files_to_generate || [],
        registry_patch: plan.registry_patch || {},
        source: "studio_factory",
        status: "private",
        visibility: "private",
      });
      const savedName = response.agent?.agent_name || plannedName;
      setSavedMessage(`Saved ${savedName} as a private agent.`);
      window.dispatchEvent(new Event("refreshAgents"));
      resolveWith(savedName);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  const exactMatches = plannerResult?.exact_matches || [];
  const similarMatches = plannerResult?.similar_matches || [];
  const finalPreview = baseAgents.concat(resolvedAgents);

  return (
    <div className="fixed inset-0 z-[70] flex items-center justify-center bg-black/75 p-4">
      <div className="flex max-h-[90vh] w-full max-w-6xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Resolve Missing Agents</h2>
            <p className="mt-1 text-sm text-slate-400">
              Resolving missing agent {Math.min(index + 1, missingAgents.length)} of {missingAgents.length}. New agents are saved privately.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="grid min-h-0 flex-1 grid-cols-1 md:grid-cols-[360px_1fr]">
          <section className="border-b border-slate-800 p-5 md:border-b-0 md:border-r">
            <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="text-xs uppercase text-slate-500">Current missing capability</div>
              <div className="mt-1 text-sm font-semibold text-slate-100">{currentMissing || "Complete"}</div>
            </div>

            <label className="mt-4 block text-sm font-semibold text-slate-200">Private agent name</label>
            <input
              value={plannedName}
              onChange={(event) => setPlannedName(event.target.value)}
              className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600"
            />

            <button
              onClick={runPlanner}
              disabled={Boolean(loading) || !currentMissing}
              className="mt-4 w-full rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
            >
              {loading === "planner" ? "Planning..." : "Run Agent Planner"}
            </button>

            <div className="mt-4 rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="text-xs font-semibold uppercase text-slate-500">Resolved so far</div>
              {resolvedAgents.length ? (
                <ul className="mt-2 space-y-1 text-xs text-emerald-200">
                  {resolvedAgents.map((agent) => (
                    <li key={agent}>{agent}</li>
                  ))}
                </ul>
              ) : (
                <div className="mt-2 text-xs text-slate-500">None yet.</div>
              )}
            </div>

            <div className="mt-4 rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="text-xs font-semibold uppercase text-slate-500">Final agents preview</div>
              <ul className="mt-2 max-h-40 space-y-1 overflow-auto text-xs text-slate-300">
                {finalPreview.map((agent) => (
                  <li key={agent}>{agent}</li>
                ))}
              </ul>
            </div>
          </section>

          <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            {error ? (
              <div className="mb-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
                {error}
              </div>
            ) : null}
            {savedMessage ? (
              <div className="mb-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
                {savedMessage}
              </div>
            ) : null}

            {complete ? (
              <div className="rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-5 text-sm text-emerald-100">
                All missing agents are resolved.
              </div>
            ) : null}

            {!plannerResult && !complete ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
                {loading === "planner" ? "Checking reusable agents..." : "Run the planner to resolve this missing capability."}
              </div>
            ) : null}

            {plannerResult ? (
              <div className="space-y-4">
                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="flex flex-wrap items-center justify-between gap-3">
                    <div>
                      <div className="text-xs uppercase text-slate-500">Recommendation</div>
                      <div className="mt-1 text-sm font-semibold text-slate-100">{plannerResult.recommendation}</div>
                    </div>
                    <div className="text-right">
                      <div className="text-xs uppercase text-slate-500">Confidence</div>
                      <div className="mt-1 text-lg font-bold text-cyan-300">
                        {Math.round((plannerResult.confidence_score || 0) * 100)}%
                      </div>
                    </div>
                  </div>
                  {plannerResult.explanation ? (
                    <p className="mt-3 text-xs leading-5 text-slate-300">{plannerResult.explanation}</p>
                  ) : null}
                </section>

                <section className="grid gap-4 lg:grid-cols-2">
                  <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                    <h4 className="mb-2 text-sm font-bold text-cyan-300">Exact Matches</h4>
                    <div className="space-y-2">
                      {exactMatches.length ? exactMatches.map((match) => (
                        <MatchCard key={match.name} match={match} onUse={resolveWith} />
                      )) : <div className="text-xs text-slate-500">None found.</div>}
                    </div>
                  </div>
                  <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                    <h4 className="mb-2 text-sm font-bold text-cyan-300">Similar Matches</h4>
                    <div className="space-y-2">
                      {similarMatches.length ? similarMatches.map((match) => (
                        <MatchCard key={match.name} match={match} onUse={resolveWith} />
                      )) : <div className="text-xs text-slate-500">None found.</div>}
                    </div>
                  </div>
                </section>

                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <h4 className="mb-3 text-sm font-bold text-cyan-300">Create Private Agent</h4>
                  <p className="text-xs leading-5 text-slate-300">
                    If no existing agent is suitable, run a safe factory dry run and save the reviewed result as a private agent.
                  </p>
                  <button
                    onClick={runFactoryDryRun}
                    disabled={Boolean(loading) || !canCreate}
                    className="mt-3 rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
                  >
                    {loading === "factory" ? "Running dry run..." : "Generate Agent Dry Run"}
                  </button>
                </section>

                {factoryResult ? (
                  <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                    <div className="flex flex-wrap items-start justify-between gap-3">
                      <div>
                        <div className="text-xs uppercase text-slate-500">Factory decision</div>
                        <div className="mt-1 text-sm font-semibold text-slate-100">
                          {factoryResult.plan?.decision || "unknown"}
                        </div>
                      </div>
                      <div className="rounded-full border border-amber-700 bg-amber-950/30 px-3 py-1 text-xs text-amber-100">
                        Review required
                      </div>
                    </div>
                    <pre className="mt-3 max-h-52 overflow-auto rounded bg-slate-950 p-3 text-xs text-slate-200">
                      {JSON.stringify(factoryResult.plan?.proposed_agent_spec || {}, null, 2)}
                    </pre>
                    <button
                      onClick={savePrivateAgent}
                      disabled={loading === "save"}
                      className="mt-3 rounded-lg bg-emerald-700 px-4 py-2 text-sm font-bold text-white hover:bg-emerald-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
                    >
                      {loading === "save" ? "Saving..." : "Save as Private Agent"}
                    </button>
                  </section>
                ) : null}
              </div>
            ) : null}
          </section>
        </div>
      </div>
    </div>
  );
}
