"use client";

import { useMemo, useState } from "react";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import type { Edge, Node } from "reactflow";
import { ApiClientError, apiPost } from "@/lib/apiClient";
import { getStableUserId } from "@/utils/userId";

type SavedWorkflowOption = {
  name: string;
  loop_type?: string | null;
};

type DagPreviewModalProps = {
  loopType: string;
  nodes: Node[];
  edges: Edge[];
  savedWorkflows?: SavedWorkflowOption[];
  selectedWorkflowName?: string | null;
  onClose: () => void;
};

type DagPreviewResponse = {
  status: string;
  valid?: boolean;
  warnings?: string[];
  errors?: string[];
  dag?: {
    nodes?: unknown[];
    edges?: unknown[];
  };
  preview?: {
    execution_order?: string[];
    parallel_groups?: string[][];
    dependency_graph?: Record<string, { agent_name?: string; depends_on?: string[]; can_run_parallel?: boolean }>;
    parallel_group_agents?: string[][];
  };
};

type DagValidateResponse = {
  status: string;
  valid: boolean;
  errors?: string[];
  warnings?: string[];
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Workflow optimization request failed.";
}

function graphPayloadFromNodes(nodes: Node[], edges: Edge[], loopType: string) {
  return {
    graph: {
      nodes: nodes.map((node) => ({
        id: node.id,
        data: {
          uiLabel: String(node.data?.uiLabel || node.data?.backendLabel || node.id),
          backendLabel: String(node.data?.backendLabel || node.data?.uiLabel || node.id),
        },
      })),
      edges: edges.map((edge) => ({
        source: edge.source,
        target: edge.target,
      })),
    },
    loop_type: loopType,
  };
}

function samplePayload(loopType: string) {
  return {
    agents: ["Digital Spec Agent", "Digital RTL Agent", "Digital Testbench Generator Agent"],
    loop_type: loopType,
    infer_parallel: true,
  };
}

function parseJson(text: string): unknown {
  try {
    return JSON.parse(text);
  } catch {
    throw new Error("Enter valid workflow JSON before running advanced preview.");
  }
}

function JsonBlock({ title, value }: { title: string; value: unknown }) {
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <h4 className="mb-2 text-sm font-bold text-cyan-300">{title}</h4>
      <pre className="max-h-72 overflow-auto whitespace-pre-wrap rounded bg-slate-950 p-3 text-xs text-slate-200">
        {JSON.stringify(value || {}, null, 2)}
      </pre>
    </section>
  );
}

function EmptyState() {
  return (
    <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
      Choose a workflow source and click Analyze Parallelism. ChipLoop will look for safe steps that can run together.
    </div>
  );
}

export default function DagPreviewModal({
  loopType,
  nodes,
  edges,
  savedWorkflows = [],
  selectedWorkflowName,
  onClose,
}: DagPreviewModalProps) {
  const supabase = createClientComponentClient();
  const [source, setSource] = useState<"current" | "saved">("current");
  const [selectedSavedWorkflow, setSelectedSavedWorkflow] = useState(selectedWorkflowName || savedWorkflows[0]?.name || "");
  const [jsonText, setJsonText] = useState(() => JSON.stringify(graphPayloadFromNodes(nodes, edges, loopType), null, 2));
  const [preview, setPreview] = useState<DagPreviewResponse | null>(null);
  const [validation, setValidation] = useState<DagValidateResponse | null>(null);
  const [loading, setLoading] = useState<"preview" | "validate" | "saved" | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [advancedOpen, setAdvancedOpen] = useState(false);

  const hasCanvasWorkflow = nodes.length > 0;
  const canAnalyze = useMemo(() => {
    if (loading) return false;
    if (source === "current") return hasCanvasWorkflow;
    return Boolean(selectedSavedWorkflow);
  }, [hasCanvasWorkflow, loading, selectedSavedWorkflow, source]);

  const dependencyGraph = preview?.preview?.dependency_graph || {};
  const executionOrder = preview?.preview?.execution_order || [];
  const parallelGroupAgents = preview?.preview?.parallel_group_agents || [];
  const resultErrors = preview?.errors || validation?.errors || [];
  const resultWarnings = preview?.warnings || validation?.warnings || [];
  const serialSteps = executionOrder.map((nodeId) => dependencyGraph[nodeId]?.agent_name || nodeId);
  const serialStageCount = serialSteps.length;
  const parallelStageCount = parallelGroupAgents.length;
  const parallelizableGroupCount = parallelGroupAgents.filter((group) => group.length > 1).length;
  const stageReduction = Math.max(0, serialStageCount - parallelStageCount);

  function resetResults() {
    setPreview(null);
    setValidation(null);
    setError(null);
  }

  async function buildSavedWorkflowPayload() {
    if (!selectedSavedWorkflow) {
      throw new Error("Choose a saved workflow first.");
    }

    setLoading("saved");
    const userId = await getStableUserId(supabase);
    const { data, error: dbError } = await supabase
      .from("workflows")
      .select("name,loop_type,definitions")
      .eq("user_id", userId)
      .eq("name", selectedSavedWorkflow)
      .maybeSingle();

    if (dbError) throw new Error(dbError.message);
    if (!data?.definitions) throw new Error("Saved workflow has no graph definitions.");

    const definitions = data.definitions as { nodes?: Node[]; edges?: Edge[] };
    return graphPayloadFromNodes(definitions.nodes || [], definitions.edges || [], data.loop_type || loopType);
  }

  async function runPreview(payloadOverride?: unknown) {
    setLoading("preview");
    setError(null);
    try {
      const payload = payloadOverride || parseJson(jsonText);
      setJsonText(JSON.stringify(payload, null, 2));
      const response = await apiPost<DagPreviewResponse>("/studio/dag/preview", payload);
      setPreview(response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  async function analyzeParallelism() {
    if (!canAnalyze) return;
    resetResults();
    try {
      const payload = source === "current"
        ? graphPayloadFromNodes(nodes, edges, loopType)
        : await buildSavedWorkflowPayload();
      await runPreview(payload);
    } catch (err) {
      setError(errorMessage(err));
      setLoading(null);
    }
  }

  async function runValidate() {
    setLoading("validate");
    setError(null);
    try {
      const payload = parseJson(jsonText);
      const response = await apiPost<DagValidateResponse>("/studio/dag/validate", payload);
      setValidation(response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  function showSaveUnavailable(mode: "copy" | "same") {
    if (mode === "same") {
      const ok = window.confirm("Save to the same workflow will require backend DAG save support. Continue?");
      if (!ok) return;
    }
    alert("DAG save is not enabled yet. This preview did not modify or execute the workflow.");
  }

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex max-h-[90vh] w-full max-w-5xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Optimize Workflow</h2>
            <p className="mt-1 text-sm text-slate-400">
              Analyze a workflow for safe parallel steps without executing agents or changing serial behavior.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          <section className="grid gap-4 rounded-lg border border-slate-800 bg-black/30 p-4 md:grid-cols-[220px_1fr_auto]">
            <div>
              <label className="mb-2 block text-xs font-semibold uppercase text-slate-500">Workflow source</label>
              <select
                value={source}
                onChange={(event) => {
                  setSource(event.target.value as "current" | "saved");
                  resetResults();
                }}
                className="w-full rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-200 outline-none focus:border-cyan-600"
              >
                <option value="current">Current workflow</option>
                <option value="saved">Saved workflow</option>
              </select>
            </div>

            <div>
              <label className="mb-2 block text-xs font-semibold uppercase text-slate-500">
                {source === "current" ? "Canvas workflow" : "Saved workflow"}
              </label>
              {source === "current" ? (
                <div className="rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-300">
                  {hasCanvasWorkflow ? `${nodes.length} agents on canvas` : "No agents on canvas"}
                </div>
              ) : (
                <select
                  value={selectedSavedWorkflow}
                  onChange={(event) => {
                    setSelectedSavedWorkflow(event.target.value);
                    resetResults();
                  }}
                  className="w-full rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-200 outline-none focus:border-cyan-600"
                >
                  {savedWorkflows.length ? (
                    savedWorkflows.map((workflow) => (
                      <option key={workflow.name} value={workflow.name}>
                        {workflow.name}
                      </option>
                    ))
                  ) : (
                    <option value="">No saved workflows</option>
                  )}
                </select>
              )}
            </div>

            <div className="flex items-end">
              <button
                onClick={analyzeParallelism}
                disabled={!canAnalyze}
                className="w-full rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500 md:w-auto"
              >
                {loading ? "Analyzing..." : "Analyze Parallelism"}
              </button>
            </div>
          </section>

          <div className="mt-4 rounded-lg border border-amber-800/60 bg-amber-950/20 p-3 text-xs text-amber-100/80">
            Preview only. DAG execution remains opt-in and this UI does not run workflows.
          </div>

          {error ? (
            <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
              {error}
            </div>
          ) : null}

          {!preview && !validation && !error ? (
            <div className="mt-4">
              <EmptyState />
            </div>
          ) : null}

          {preview ? (
            <div className="mt-5 space-y-4">
              <section className="grid gap-4 md:grid-cols-3">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Validation</div>
                  <div className={`mt-2 text-lg font-bold ${preview.valid ? "text-emerald-300" : "text-amber-300"}`}>
                    {preview.valid ? "Safe to review" : "Needs attention"}
                  </div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Estimated benefit</div>
                  <div className="mt-2 text-lg font-bold text-cyan-300">
                    {stageReduction > 0 ? `${stageReduction} fewer stages` : "No stage reduction yet"}
                  </div>
                  <div className="mt-1 text-xs text-slate-400">
                    {serialStageCount} serial steps to {parallelStageCount || 0} parallel stages
                  </div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Parallel groups</div>
                  <div className="mt-2 text-lg font-bold text-cyan-300">{parallelizableGroupCount}</div>
                  <div className="mt-1 text-xs text-slate-400">Groups with more than one agent</div>
                </div>
              </section>

              <section className="grid gap-4 lg:grid-cols-2">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <h3 className="mb-3 text-sm font-bold text-cyan-300">Current Serial Steps</h3>
                  {serialSteps.length ? (
                    <ol className="space-y-2 text-sm text-slate-300">
                      {serialSteps.map((step, index) => (
                        <li key={`${step}-${index}`} className="rounded border border-slate-800 bg-slate-950 px-3 py-2">
                          <span className="mr-2 text-slate-500">Step {index + 1}</span>
                          {step}
                        </li>
                      ))}
                    </ol>
                  ) : (
                    <div className="text-sm text-slate-500">No serial order returned.</div>
                  )}
                </div>

                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <h3 className="mb-3 text-sm font-bold text-cyan-300">Recommended Parallel Groups</h3>
                  {parallelGroupAgents.length ? (
                    <div className="space-y-3 text-sm text-slate-300">
                      {parallelGroupAgents.map((group, index) => (
                        <div key={`group-${index}`} className="rounded border border-slate-800 bg-slate-950 p-3">
                          <div className="mb-2 text-xs font-semibold uppercase text-slate-500">Stage {index + 1}</div>
                          <div className="flex flex-wrap gap-2">
                            {group.map((agent) => (
                              <span key={`${index}-${agent}`} className="rounded-full border border-cyan-900/60 bg-cyan-950/30 px-2 py-1 text-xs text-cyan-100">
                                {agent}
                              </span>
                            ))}
                          </div>
                        </div>
                      ))}
                    </div>
                  ) : (
                    <div className="text-sm text-slate-500">No parallel groups returned.</div>
                  )}
                </div>
              </section>

              <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                <h3 className="mb-3 text-sm font-bold text-cyan-300">Warnings</h3>
                {resultWarnings.length || resultErrors.length ? (
                  <ul className="space-y-2 text-sm">
                    {[...resultWarnings, ...resultErrors].map((item, index) => (
                      <li key={`${item}-${index}`} className="rounded border border-amber-900/60 bg-amber-950/20 px-3 py-2 text-amber-100">
                        {item}
                      </li>
                    ))}
                  </ul>
                ) : (
                  <div className="text-sm text-slate-400">
                    No blocking warnings returned. Review the suggested groups before saving any future DAG version.
                  </div>
                )}
              </section>

              <section className="flex flex-wrap justify-end gap-2">
                <button
                  onClick={() => showSaveUnavailable("copy")}
                  className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500"
                >
                  Save as Copy
                </button>
                <button
                  onClick={() => showSaveUnavailable("same")}
                  className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900"
                >
                  Save to Same Workflow
                </button>
                <button
                  onClick={() => setAdvancedOpen((open) => !open)}
                  className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900"
                >
                  {advancedOpen ? "Hide Advanced" : "Advanced"}
                </button>
              </section>
            </div>
          ) : null}

          <section className="mt-5 rounded-lg border border-slate-800 bg-black/20">
            <button
              onClick={() => setAdvancedOpen((open) => !open)}
              className="flex w-full items-center justify-between px-4 py-3 text-left text-sm font-semibold text-slate-200 hover:bg-slate-900"
            >
              <span>Advanced JSON and Dependency Details</span>
              <span className="text-slate-500">{advancedOpen ? "Hide" : "Show"}</span>
            </button>

            {advancedOpen ? (
              <div className="space-y-4 border-t border-slate-800 p-4">
                <div>
                  <label className="block text-sm font-semibold text-slate-200">Workflow plan JSON</label>
                  <textarea
                    value={jsonText}
                    onChange={(event) => setJsonText(event.target.value)}
                    className="mt-2 h-56 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 font-mono text-xs outline-none focus:border-cyan-600"
                    spellCheck={false}
                  />
                  <div className="mt-3 flex flex-wrap gap-2">
                    <button
                      onClick={() => {
                        setJsonText(JSON.stringify(graphPayloadFromNodes(nodes, edges, loopType), null, 2));
                        resetResults();
                      }}
                      disabled={!hasCanvasWorkflow}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                    >
                      Use current workflow JSON
                    </button>
                    <button
                      onClick={() => {
                        setJsonText(JSON.stringify(samplePayload(loopType), null, 2));
                        resetResults();
                      }}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900"
                    >
                      Use sample JSON
                    </button>
                    <button
                      onClick={() => runPreview()}
                      disabled={Boolean(loading) || !jsonText.trim()}
                      className="rounded-lg bg-cyan-600 px-3 py-2 text-xs font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
                    >
                      Run Advanced Preview
                    </button>
                    <button
                      onClick={runValidate}
                      disabled={Boolean(loading) || !jsonText.trim()}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                    >
                      Validate
                    </button>
                  </div>
                </div>

                {preview || validation ? (
                  <div className="space-y-4">
                    <section className="grid gap-4 lg:grid-cols-2">
                      <JsonBlock title="Nodes" value={preview?.dag?.nodes || []} />
                      <JsonBlock title="Edges" value={preview?.dag?.edges || []} />
                    </section>
                    <section className="grid gap-4 lg:grid-cols-2">
                      <JsonBlock title="Parallel Groups" value={preview?.preview?.parallel_groups || []} />
                      <JsonBlock title="Dependency Graph" value={preview?.preview?.dependency_graph || {}} />
                    </section>
                  </div>
                ) : null}
              </div>
            ) : null}
          </section>
        </div>
      </div>
    </div>
  );
}
