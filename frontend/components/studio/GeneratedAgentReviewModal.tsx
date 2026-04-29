"use client";

import { useState } from "react";
import { ApiClientError, apiPost } from "@/lib/apiClient";

export type GeneratedAgentReviewItem = {
  agentName: string;
  request: string;
  loopType: string;
  domain?: string;
  createdAt: string;
  result: {
    ok: boolean;
    dry_run: boolean;
    plan: {
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
    errors?: string[];
  };
};

function JsonReviewBlock({
  title,
  value,
  onCopy,
}: {
  title: string;
  value: unknown;
  onCopy: (label: string, text: string) => void;
}) {
  const text = typeof value === "string" ? value : JSON.stringify(value || {}, null, 2);
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="mb-2 flex items-center justify-between gap-3">
        <h4 className="text-sm font-bold text-cyan-300">{title}</h4>
        <button
          onClick={() => onCopy(title, text)}
          className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-900"
        >
          Copy
        </button>
      </div>
      <pre className="max-h-72 overflow-auto whitespace-pre-wrap rounded bg-slate-950 p-3 text-xs text-slate-200">
        {text}
      </pre>
    </section>
  );
}

function ListReviewBlock({ title, items }: { title: string; items?: string[] }) {
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

export default function GeneratedAgentReviewModal({
  latestItem,
  onClose,
}: {
  latestItem: GeneratedAgentReviewItem | null;
  onClose: () => void;
}) {
  const [copied, setCopied] = useState<string | null>(null);
  const [saving, setSaving] = useState(false);
  const [savedStatus, setSavedStatus] = useState<string | null>(null);
  const [saveError, setSaveError] = useState<string | null>(null);

  async function copyText(label: string, text: string) {
    await navigator.clipboard.writeText(text);
    setCopied(label);
    window.setTimeout(() => setCopied(null), 1500);
  }

  function errorMessage(error: unknown): string {
    if (error instanceof ApiClientError && error.status === 401) {
      return "Your session expired. Please sign in again.";
    }
    if (error instanceof Error) return error.message;
    return "Failed to save private agent.";
  }

  async function savePrivateAgent() {
    if (!latestItem) return;
    setSaving(true);
    setSaveError(null);
    setSavedStatus(null);
    try {
      const plan = latestItem.result.plan;
      const spec = plan.proposed_agent_spec || {};
      const response = await apiPost<{ status: string; agent: { agent_name?: string; status?: string } }>("/studio/user-agents", {
        name: latestItem.agentName,
        loop_type: latestItem.loopType,
        domain: latestItem.domain || latestItem.loopType,
        description: String(spec.description || latestItem.request),
        agent_spec: spec,
        skills: plan.proposed_skill_specs || [],
        tools: plan.proposed_tool_refs || [],
        hooks: plan.proposed_hook_refs || [],
        generated_files: plan.files_to_generate || [],
        registry_patch: plan.registry_patch || {},
        source: "studio_factory",
        status: "private",
        visibility: "private",
      });
      setSavedStatus(`Saved ${response.agent?.agent_name || latestItem.agentName} as a private agent.`);
      window.dispatchEvent(new Event("refreshAgents"));
    } catch (error) {
      setSaveError(errorMessage(error));
    } finally {
      setSaving(false);
    }
  }

  const plan = latestItem?.result.plan;
  const risks = (plan?.risk_notes || []).concat(latestItem?.result.errors || []);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex max-h-[90vh] w-full max-w-6xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Generated Agents</h2>
            <p className="mt-1 text-sm text-slate-400">
              Review dry-run output before any manual promotion work.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {!latestItem ? (
            <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
              No generated agent dry-run is available in this Studio session. Run Agent Planner, then Agent Factory Dry Run to review output here.
            </div>
          ) : (
            <div className="space-y-4">
              {copied ? (
                <div className="rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
                  Copied {copied}.
                </div>
              ) : null}
              {savedStatus ? (
                <div className="rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
                  {savedStatus}
                </div>
              ) : null}
              {saveError ? (
                <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
                  {saveError}
                </div>
              ) : null}

              <section className="rounded-lg border border-amber-800/60 bg-amber-950/20 p-4">
                <div className="flex flex-wrap items-start justify-between gap-4">
                  <div>
                    <div className="text-xs uppercase text-amber-200/80">Manual Review Required</div>
                    <h3 className="mt-1 text-lg font-bold text-slate-100">{latestItem.agentName}</h3>
                    <div className="mt-1 text-xs text-slate-400">
                      {latestItem.loopType}
                      {latestItem.domain ? ` | ${latestItem.domain}` : ""} | {new Date(latestItem.createdAt).toLocaleString()}
                    </div>
                  </div>
                  <div className="rounded-full border border-amber-700 bg-amber-950/40 px-3 py-1 text-xs text-amber-100">
                    Review-only
                  </div>
                </div>
                <p className="mt-3 text-sm text-slate-300">{latestItem.request}</p>
                <button
                  onClick={savePrivateAgent}
                  disabled={saving}
                  className="mt-4 rounded-lg bg-emerald-700 px-4 py-2 text-sm font-bold text-white hover:bg-emerald-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
                >
                  {saving ? "Saving..." : "Save as Private Agent"}
                </button>
              </section>

              <JsonReviewBlock
                title="AgentSpec JSON"
                value={plan?.proposed_agent_spec || {}}
                onCopy={copyText}
              />

              <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
                <h4 className="mb-2 text-sm font-bold text-cyan-300">Generated Files</h4>
                {plan?.files_to_generate?.length ? (
                  <div className="space-y-2">
                    {plan.files_to_generate.map((file, index) => (
                      <div key={`${file.path || "file"}-${index}`} className="rounded-md border border-slate-800 bg-slate-950 p-3">
                        <div className="flex items-start justify-between gap-3">
                          <div>
                            <div className="text-xs font-semibold text-slate-100">{file.path || "planned file"}</div>
                            <div className="mt-1 text-xs text-slate-400">{file.description || "No description."}</div>
                          </div>
                          {file.content_preview ? (
                            <button
                              onClick={() => copyText(file.path || "file content", file.content_preview || "")}
                              className="shrink-0 rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-900"
                            >
                              Copy
                            </button>
                          ) : null}
                        </div>
                        {file.content_preview ? (
                          <pre className="mt-2 max-h-40 overflow-auto whitespace-pre-wrap rounded bg-black/40 p-2 text-[11px] text-slate-300">
                            {file.content_preview}
                          </pre>
                        ) : null}
                      </div>
                    ))}
                  </div>
                ) : (
                  <div className="text-xs text-slate-500">No generated files proposed.</div>
                )}
              </section>

              <JsonReviewBlock
                title="Registry Patch YAML"
                value={plan?.registry_patch?.content || ""}
                onCopy={copyText}
              />

              <section className="grid gap-4 lg:grid-cols-2">
                <ListReviewBlock title="Validation Checklist" items={plan?.validation_checklist || []} />
                <ListReviewBlock title="Risks" items={risks} />
              </section>

              <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
                <h4 className="mb-2 text-sm font-bold text-cyan-300">Migration Notes</h4>
                <ul className="space-y-1 text-xs text-slate-300">
                  <li>Review AgentSpec, generated files, and registry patch manually.</li>
                  <li>No generated files have been saved by this UI.</li>
                  <li>No registry patch has been promoted or merged.</li>
                  <li>Use a manual developer workflow for production promotion after review.</li>
                </ul>
              </section>
            </div>
          )}
        </section>
      </div>
    </div>
  );
}
