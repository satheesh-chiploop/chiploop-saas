"use client";

import { useMemo, useState } from "react";
import type { Edge, Node } from "reactflow";
import { ApiClientError, apiPost } from "@/lib/apiClient";

type DagPreviewModalProps = {
  loopType: string;
  nodes: Node[];
  edges: Edge[];
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
    dependency_graph?: Record<string, unknown>;
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
  return "DAG request failed.";
}

function graphFromCanvas(nodes: Node[], edges: Edge[]) {
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
    throw new Error("Enter valid workflow JSON before running DAG preview.");
  }
}

function ListBlock({ title, items }: { title: string; items?: string[] }) {
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <h4 className="mb-2 text-sm font-bold text-cyan-300">{title}</h4>
      {items?.length ? (
        <ol className="space-y-1 text-xs text-slate-300">
          {items.map((item, index) => (
            <li key={`${title}-${item}-${index}`} className="rounded border border-slate-800 bg-slate-950 px-2 py-1">
              {item}
            </li>
          ))}
        </ol>
      ) : (
        <div className="text-xs text-slate-500">None.</div>
      )}
    </section>
  );
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

export default function DagPreviewModal({ loopType, nodes, edges, onClose }: DagPreviewModalProps) {
  const [jsonText, setJsonText] = useState(() => JSON.stringify(samplePayload(loopType), null, 2));
  const [preview, setPreview] = useState<DagPreviewResponse | null>(null);
  const [validation, setValidation] = useState<DagValidateResponse | null>(null);
  const [loading, setLoading] = useState<"preview" | "validate" | null>(null);
  const [error, setError] = useState<string | null>(null);

  const hasCanvasWorkflow = nodes.length > 0;
  const canRun = useMemo(() => jsonText.trim().length > 0 && !loading, [jsonText, loading]);

  function useCurrentWorkflow() {
    const payload = graphFromCanvas(nodes, edges);
    setJsonText(JSON.stringify({ ...payload, loop_type: loopType }, null, 2));
    setPreview(null);
    setValidation(null);
    setError(null);
  }

  function useSample() {
    setJsonText(JSON.stringify(samplePayload(loopType), null, 2));
    setPreview(null);
    setValidation(null);
    setError(null);
  }

  async function runPreview() {
    if (!canRun) return;
    setLoading("preview");
    setError(null);
    try {
      const payload = parseJson(jsonText);
      const response = await apiPost<DagPreviewResponse>("/studio/dag/preview", payload);
      setPreview(response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  async function runValidate() {
    if (!canRun) return;
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

  const resultErrors = preview?.errors || validation?.errors || [];
  const resultWarnings = preview?.warnings || validation?.warnings || [];

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex max-h-[90vh] w-full max-w-6xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">DAG Preview</h2>
            <p className="mt-1 text-sm text-slate-400">
              Validate dependency graphs and preview parallel groups without executing agents.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="grid min-h-0 flex-1 grid-cols-1 md:grid-cols-[420px_1fr]">
          <section className="border-b border-slate-800 p-5 md:border-b-0 md:border-r">
            <div className="mb-3 flex flex-wrap gap-2">
              <button
                onClick={useCurrentWorkflow}
                disabled={!hasCanvasWorkflow}
                className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
              >
                Use current Studio workflow
              </button>
              <button
                onClick={useSample}
                className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900"
              >
                Use sample
              </button>
            </div>

            <label className="block text-sm font-semibold text-slate-200">Workflow plan JSON</label>
            <textarea
              value={jsonText}
              onChange={(event) => setJsonText(event.target.value)}
              className="mt-2 h-[44vh] w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 font-mono text-xs outline-none focus:border-cyan-600"
              spellCheck={false}
            />

            <div className="mt-4 flex gap-2">
              <button
                onClick={runPreview}
                disabled={!canRun}
                className="flex-1 rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
              >
                {loading === "preview" ? "Previewing..." : "Run Preview"}
              </button>
              <button
                onClick={runValidate}
                disabled={!canRun}
                className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
              >
                {loading === "validate" ? "Validating..." : "Validate"}
              </button>
            </div>

            <div className="mt-4 rounded-lg border border-amber-800/60 bg-amber-950/20 p-3 text-xs text-amber-100/80">
              Preview only. This UI does not run workflows or execute agents.
            </div>
          </section>

          <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            {error ? (
              <div className="mb-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
                {error}
              </div>
            ) : null}

            {!preview && !validation && !error ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
                Paste workflow JSON or use the current Studio workflow, then run preview or validation.
              </div>
            ) : null}

            {(preview || validation) ? (
              <div className="space-y-4">
                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="flex flex-wrap items-center justify-between gap-3">
                    <div>
                      <div className="text-xs uppercase text-slate-500">Validation</div>
                      <div className={`mt-1 text-sm font-semibold ${preview?.valid || validation?.valid ? "text-emerald-300" : "text-amber-300"}`}>
                        {preview?.valid ?? validation?.valid ? "Valid" : "Needs attention"}
                      </div>
                    </div>
                    <div className="text-right">
                      <div className="text-xs uppercase text-slate-500">Mode</div>
                      <div className="mt-1 text-sm font-bold text-cyan-300">Preview only</div>
                    </div>
                  </div>
                </section>

                <section className="grid gap-4 lg:grid-cols-2">
                  <JsonBlock title="Nodes" value={preview?.dag?.nodes || []} />
                  <JsonBlock title="Edges" value={preview?.dag?.edges || []} />
                </section>

                <section className="grid gap-4 lg:grid-cols-2">
                  <ListBlock title="Serial Execution Order" items={preview?.preview?.execution_order || []} />
                  <JsonBlock title="Parallel Groups" value={preview?.preview?.parallel_groups || []} />
                </section>

                <JsonBlock title="Parallel Group Agents" value={preview?.preview?.parallel_group_agents || []} />
                <JsonBlock title="Dependency Graph" value={preview?.preview?.dependency_graph || {}} />

                <section className="grid gap-4 lg:grid-cols-2">
                  <ListBlock title="Dependency Warnings" items={resultWarnings} />
                  <ListBlock title="Validation Errors" items={resultErrors} />
                </section>
              </div>
            ) : null}
          </section>
        </div>
      </div>
    </div>
  );
}
