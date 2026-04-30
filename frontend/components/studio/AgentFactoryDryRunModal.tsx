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
  files_to_generate?: Array<{ path?: string; description?: string; content_preview?: string }>;
  registry_patch?: { path?: string; content?: string } | null;
  validation_checklist?: string[];
  risk_notes?: string[];
};

type FactoryResult = {
  ok: boolean;
  dry_run: boolean;
  plan: FactoryPlan;
  written_files?: string[];
  errors?: string[];
};

type FactoryResponse = { status: string; result: FactoryResult };

type SavePrivateAgentResponse = {
  status: string;
  agent?: { agent_name?: string; status?: string };
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) return "Your session expired. Please sign in again.";
  if (error instanceof Error) return error.message;
  return "Request failed.";
}

function ChipList({ title, items }: { title: string; items?: string[] }) {
  return (
    <div>
      <div className="mb-2 text-xs font-semibold uppercase text-slate-400">{title}</div>
      {items?.length ? (
        <div className="flex flex-wrap gap-1.5">
          {items.map((item) => (
            <span key={`${title}-${item}`} className="rounded-full border border-slate-700 bg-slate-950 px-2 py-1 text-[11px] text-slate-200">
              {item}
            </span>
          ))}
        </div>
      ) : (
        <div className="text-xs text-slate-500">None</div>
      )}
    </div>
  );
}

function AdvancedBlock({ title, value, onCopy }: { title: string; value: unknown; onCopy: (label: string, text: string) => void }) {
  const text = typeof value === "string" ? value : JSON.stringify(value || {}, null, 2);
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <div className="mb-2 flex items-center justify-between gap-3">
        <h4 className="text-sm font-bold text-cyan-300">{title}</h4>
        <button onClick={() => onCopy(title, text)} className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-900">
          Copy
        </button>
      </div>
      <pre className="max-h-56 overflow-auto whitespace-pre-wrap rounded-md bg-slate-950 p-3 text-xs text-slate-200">{text}</pre>
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
  const [saving, setSaving] = useState(false);
  const [showAdvanced, setShowAdvanced] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [copied, setCopied] = useState<string | null>(null);
  const [savedMessage, setSavedMessage] = useState<string | null>(null);

  const canRun = useMemo(() => name.trim().length > 0 && requestText.trim().length > 0 && !loading, [name, requestText, loading]);
  const plan = result?.plan;
  const spec = plan?.proposed_agent_spec || {};
  const risks = (plan?.risk_notes || []).concat(result?.errors || []);

  async function copyText(label: string, text: string) {
    await navigator.clipboard.writeText(text);
    setCopied(label);
    window.setTimeout(() => setCopied(null), 1500);
  }

  async function runDryRun() {
    if (!canRun) return;
    setLoading(true);
    setError(null);
    setSavedMessage(null);
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

  async function savePrivateAgent() {
    if (!result) return;
    setSaving(true);
    setError(null);
    setSavedMessage(null);
    try {
      const response = await apiPost<SavePrivateAgentResponse>("/studio/user-agents", {
        name: name.trim(),
        loop_type: loopType,
        domain: domain.trim() || loopType,
        description: String(spec.description || requestText.trim()),
        agent_spec: spec,
        skills: plan?.proposed_skill_specs || [],
        tools: plan?.proposed_tool_refs || [],
        hooks: plan?.proposed_hook_refs || [],
        generated_files: plan?.files_to_generate || [],
        registry_patch: plan?.registry_patch || {},
        source: "studio_factory",
        status: "private",
        visibility: "private",
      });
      setSavedMessage(`Saved ${response.agent?.agent_name || name.trim()} as a private agent.`);
      window.dispatchEvent(new Event("refreshAgents"));
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setSaving(false);
    }
  }

  return (
    <div className="fixed inset-0 z-[60] flex items-center justify-center bg-black/75 p-4">
      <div className="flex max-h-[90vh] w-full max-w-5xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Review Draft Agent</h2>
            <p className="mt-1 text-sm text-slate-400">Generate a safe draft, review the summary, then save it as your private agent.</p>
          </div>
          <button onClick={onClose} className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900">Close</button>
        </div>

        <div className="grid min-h-0 flex-1 grid-cols-1 md:grid-cols-[360px_1fr]">
          <section className="border-b border-slate-800 p-5 md:border-b-0 md:border-r">
            <label className="block text-sm font-semibold text-slate-200">Agent name</label>
            <input value={name} onChange={(event) => setName(event.target.value)} className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600" placeholder="New agent name" />

            <label className="mt-4 block text-sm font-semibold text-slate-200">Loop</label>
            <select value={loopType} onChange={(event) => setLoopType(event.target.value)} className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600">
              {LOOP_OPTIONS.map((option) => <option key={option} value={option}>{option[0].toUpperCase() + option.slice(1)}</option>)}
            </select>

            <label className="mt-4 block text-sm font-semibold text-slate-200">Domain</label>
            <input value={domain} onChange={(event) => setDomain(event.target.value)} className="mt-2 w-full rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm outline-none focus:border-cyan-600" placeholder="Optional domain" />

            <label className="mt-4 block text-sm font-semibold text-slate-200">Description</label>
            <textarea value={requestText} onChange={(event) => setRequestText(event.target.value)} className="mt-2 h-40 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 text-sm outline-none focus:border-cyan-600" placeholder="Describe the agent to draft..." />

            <button onClick={runDryRun} disabled={!canRun} className="mt-4 w-full rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500">
              {loading ? "Generating draft..." : "Generate Draft Agent"}
            </button>

            <div className="mt-4 rounded-lg border border-amber-800/60 bg-amber-950/20 p-3 text-xs text-amber-100/80">
              Draft only. Nothing is written to production folders or promoted globally.
            </div>
          </section>

          <section className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            {error ? <div className="mb-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">{error}</div> : null}
            {copied ? <div className="mb-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">Copied {copied}.</div> : null}
            {savedMessage ? <div className="mb-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">{savedMessage}</div> : null}

            {!result && !error ? (
              <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
                Generate a draft to review its purpose, skills, tools, warnings, and save option.
              </div>
            ) : null}

            {result ? (
              <div className="space-y-4">
                <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="flex flex-wrap items-start justify-between gap-4">
                    <div>
                      <div className="text-xs uppercase text-slate-500">Draft Agent</div>
                      <h3 className="mt-1 text-lg font-bold text-slate-100">{name.trim()}</h3>
                      <p className="mt-2 text-sm leading-6 text-slate-300">{String(spec.description || requestText.trim())}</p>
                    </div>
                    <span className="rounded-full border border-amber-700 bg-amber-950/40 px-3 py-1 text-xs text-amber-100">Manual review required</span>
                  </div>
                </section>

                <section className="grid gap-4 md:grid-cols-3">
                  <ChipList title="Skills" items={(plan?.proposed_skill_specs || []).map((item) => String(item.name || item.id || "skill"))} />
                  <ChipList title="Tools" items={plan?.proposed_tool_refs || []} />
                  <ChipList title="Hooks" items={plan?.proposed_hook_refs || []} />
                </section>

                <section className="grid gap-4 md:grid-cols-2">
                  <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                    <h4 className="mb-2 text-sm font-bold text-cyan-300">Validation Checklist</h4>
                    {(plan?.validation_checklist || []).length ? <ul className="space-y-1 text-xs text-slate-300">{plan?.validation_checklist?.map((item) => <li key={item}>{item}</li>)}</ul> : <div className="text-xs text-slate-500">No checklist returned.</div>}
                  </div>
                  <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                    <h4 className="mb-2 text-sm font-bold text-cyan-300">Warnings</h4>
                    {risks.length ? <ul className="space-y-1 text-xs text-amber-100">{risks.map((item) => <li key={item}>{item}</li>)}</ul> : <div className="text-xs text-slate-500">No warnings returned.</div>}
                  </div>
                </section>

                <div className="flex flex-wrap gap-2">
                  <button onClick={savePrivateAgent} disabled={saving} className="rounded-lg bg-emerald-700 px-4 py-2 text-sm font-bold text-white hover:bg-emerald-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500">
                    {saving ? "Saving..." : "Save as Private Agent"}
                  </button>
                  <button onClick={() => setShowAdvanced((current) => !current)} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900">
                    {showAdvanced ? "Hide Advanced Details" : "Advanced Details"}
                  </button>
                </div>

                {showAdvanced ? (
                  <div className="space-y-4 border-t border-slate-800 pt-4">
                    <AdvancedBlock title="AgentSpec JSON" value={spec} onCopy={copyText} />
                    <AdvancedBlock title="Generated Files" value={plan?.files_to_generate || []} onCopy={copyText} />
                    <AdvancedBlock title="Registry Patch" value={plan?.registry_patch?.content || plan?.registry_patch || {}} onCopy={copyText} />
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
