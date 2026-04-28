"use client";

import { useMemo, useState } from "react";
import { ApiClientError, apiPost } from "@/lib/apiClient";

const LOOP_OPTIONS = ["digital", "analog", "embedded", "system", "validation"];

type FactoryInitialRequest = {
  name: string;
  natural_language_request: string;
  loop_type: string;
  domain?: string;
  inputs?: string[];
  outputs?: string[];
  required_skills?: string[];
  required_tools?: string[];
  required_hooks?: string[];
  allow_extension?: boolean;
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
  exact_match?: string | null;
  similar_matches?: string[];
};

type FactoryResult = {
  ok: boolean;
  dry_run: boolean;
  plan: FactoryPlan;
  written_files?: string[];
  errors?: string[];
};

type FactoryResponse = {
  status: string;
  result: FactoryResult;
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Factory dry-run failed.";
}

function JsonBlock({
  title,
  value,
  onCopy,
}: {
  title: string;
  value: unknown;
  onCopy: (text: string) => void;
}) {
  const text = typeof value === "string" ? value : JSON.stringify(value || {}, null, 2);
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="mb-2 flex items-center justify-between gap-3">
        <h4 className="text-sm font-bold text-cyan-300">{title}</h4>
        <button
          onClick={() => onCopy(text)}
          className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-900"
        >
          Copy
        </button>
      </div>
      <pre className="max-h-72 overflow-auto whitespace-pre-wrap rounded-md bg-slate-950 p-3 text-xs text-slate-200">
        {text}
      </pre>
    </section>
  );
}

function ListSection({ title, items }: { title: string; items?: string[] }) {
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <h4 className="mb-2 text-sm font-bold text-cyan-300">{title}</h4>
      {items?.length ? (
        <ul className="space-y-1 text-xs text-slate-300">
          {items.map((item) => (
            <li key={item} className="rounded border border-slate-800 bg-slate-950 px-2 py-1">
              {item}
            </li>
          ))}
        </ul>
      ) : (
        <div className="text-xs text-slate-500">None.</div>
      )}
    </section>
  );
}

export default function AgentFactoryDryRunModal({
  initialRequest,
  onClose,
}: {
  initialRequest: FactoryInitialRequest;
  onClose: () => void;
}) {
  const [name, setName] = useState(initialRequest.name || "");
  const [requestText, setRequestText] = useState(initialRequest.natural_language_request || "");
  const [loopType, setLoopType] = useState(initialRequest.loop_type || "digital");
  const [domain, setDomain] = useState(initialRequest.domain || "");
  const [result, setResult] = useState<FactoryResult | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [copied, setCopied] = useState<string | null>(null);

  const canRun = useMemo(
    () => name.trim().length > 0 && requestText.trim().length > 0 && !loading,
    [name, requestText, loading]
  );

  async function copyText(label: string, text: string) {
    await navigator.clipboard.writeText(text);
    setCopied(label);
    window.setTimeout(() => setCopied(null), 1500);
  }

  async function runDryRun() {
    if (!canRun) return;
    setLoading(true);
    setError(null);
    setCopied(null);
    try {
      const response = await apiPost<FactoryResponse>("/studio/agent-factory/dry-run", {
        dry_run: true,
        request: {
          name: name.trim(),
          natural_language_request: requestText.trim(),
          loop_type: loopType,
          domain: domain.trim() || undefined,
          inputs: initialRequest.inputs || [],
          outputs: initialRequest.outputs || [],
          required_skills: initialRequest.required_skills || [],
          required_tools: initialRequest.required_tools || [],
          required_hooks: initialRequest.required_hooks || [],
          allow_extension: Boolean(initialRequest.allow_extension),
        },
      });
      setResult(response.result);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  const plan = result?.plan;
  const writtenFiles = result?.written_files || [];

  return (
    <div className="fixed inset-0 z-[60] flex items-center justify-center bg-black/75 p-4">
      <div className="flex max-h-[90vh] w-full max-w-6xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Agent Factory Dry Run</h2>
            <p className="mt-1 text-sm text-slate-400">
              Review proposed agent files and registry patches without writing anything.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="grid min-h-0 flex-1 grid-cols-1 md:grid-cols-[380px_1fr]">
          <section className="border-b border-slate-800 p-5 md:border-b-0 md:border-r">
            <label className="block text-sm font-semibold text-slate-200">Agent name</label>
            <input
              value={name}
              onChange={(event) => setName(event.target.value)}
              className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600"
              placeholder="New agent name"
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

            <label className="mt-4 block text-sm font-semibold text-slate-200">Description / request</label>
            <textarea
              value={requestText}
              onChange={(event) => setRequestText(event.target.value)}
              className="mt-2 h-44 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 text-sm outline-none focus:border-cyan-600"
              placeholder="Describe the agent to generate..."
            />

            <button
              onClick={runDryRun}
              disabled={!canRun}
              className="mt-4 w-full rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
            >
              {loading ? "Running dry run..." : "Run dry run"}
            </button>

            <div className="mt-4 rounded-lg border border-amber-800/60 bg-amber-950/20 p-3 text-xs text-amber-100/80">
              Dry-run only. This UI does not write files, save generated code, or promote registry patches.
            </div>
          </section>

          <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            {error ? (
              <div className="mb-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
                {error}
              </div>
            ) : null}
            {copied ? (
              <div className="mb-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
                Copied {copied}.
              </div>
            ) : null}
            {!result && !error ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
                Run a dry-run to review the proposed AgentSpec, generated file plan, registry patch, checklist, and risks.
              </div>
            ) : null}

            {result ? (
              <div className="space-y-4">
                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="flex flex-wrap items-center justify-between gap-3">
                    <div>
                      <div className="text-xs uppercase text-slate-500">Decision</div>
                      <div className="mt-1 text-sm font-semibold text-slate-100">
                        {plan?.decision || "unknown"}
                      </div>
                    </div>
                    <div className="text-right">
                      <div className="text-xs uppercase text-slate-500">Dry run</div>
                      <div className="mt-1 text-sm font-bold text-cyan-300">
                        {result.dry_run ? "Yes" : "Backend returned non-dry-run"}
                      </div>
                    </div>
                  </div>
                  {writtenFiles.length ? (
                    <div className="mt-3 rounded-lg border border-amber-900/70 bg-amber-950/30 p-3 text-xs text-amber-100">
                      Backend response included written file metadata. This UI did not request write mode and will not use it.
                    </div>
                  ) : null}
                </section>

                <JsonBlock
                  title="Proposed AgentSpec"
                  value={plan?.proposed_agent_spec || {}}
                  onCopy={(text) => copyText("AgentSpec JSON", text)}
                />

                <section className="grid gap-4 lg:grid-cols-3">
                  <JsonBlock
                    title="Proposed Skills"
                    value={plan?.proposed_skill_specs || []}
                    onCopy={(text) => copyText("skills JSON", text)}
                  />
                  <ListSection title="Proposed Tools" items={plan?.proposed_tool_refs || []} />
                  <ListSection title="Proposed Hooks" items={plan?.proposed_hook_refs || []} />
                </section>

                <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <h4 className="mb-2 text-sm font-bold text-cyan-300">Generated File Plan</h4>
                  {plan?.files_to_generate?.length ? (
                    <div className="space-y-2">
                      {plan.files_to_generate.map((file, index) => (
                        <div key={`${file.path || "file"}-${index}`} className="rounded-md border border-slate-800 bg-slate-950 p-3">
                          <div className="text-xs font-semibold text-slate-100">{file.path || "planned file"}</div>
                          <div className="mt-1 text-xs text-slate-400">{file.description || "No description."}</div>
                          {file.content_preview ? (
                            <pre className="mt-2 max-h-32 overflow-auto whitespace-pre-wrap rounded bg-black/40 p-2 text-[11px] text-slate-300">
                              {file.content_preview}
                            </pre>
                          ) : null}
                        </div>
                      ))}
                    </div>
                  ) : (
                    <div className="text-xs text-slate-500">No files proposed.</div>
                  )}
                </section>

                {plan?.registry_patch ? (
                  <JsonBlock
                    title="Registry Patch Plan"
                    value={plan.registry_patch.content || plan.registry_patch}
                    onCopy={(text) => copyText("registry patch", text)}
                  />
                ) : (
                  <ListSection title="Registry Patch Plan" items={[]} />
                )}

                <section className="grid gap-4 lg:grid-cols-2">
                  <ListSection title="Validation Checklist" items={plan?.validation_checklist || []} />
                  <ListSection title="Risks" items={(plan?.risk_notes || []).concat(result.errors || [])} />
                </section>
              </div>
            ) : null}
          </section>
        </div>
      </div>
    </div>
  );
}
