"use client";

import { useMemo, useState } from "react";

type WorkflowConfigField = {
  key: string;
  label?: string;
  type?: string;
  required?: boolean;
  options?: Array<string | { value: string; label?: string; disabled?: boolean }>;
};

type WorkflowConfigSchema = {
  version?: number;
  fields?: WorkflowConfigField[];
};

type CreateAppResponse = {
  status?: string;
  app?: {
    id?: string;
    name?: string;
    slug?: string;
    status?: string;
    visibility?: string;
  };
  detail?: string;
  message?: string;
};

type Props = {
  workflowId: string | null;
  workflowName: string | null;
  loopType: string;
  configSchema: WorkflowConfigSchema;
  defaultConfig: Record<string, string | number | boolean>;
  workflowSnapshot: unknown;
  authHeaders: () => Promise<Record<string, string>>;
  onClose: () => void;
  onConfigureWorkflow?: () => void;
};

function defaultDescription(workflowName: string | null, loopType: string) {
  if (!workflowName) return "";
  return `Private ${loopType} app built from the ${workflowName} Studio workflow.`;
}

function appNameFromWorkflow(workflowName: string | null) {
  if (!workflowName) return "";
  return workflowName
    .replace(/_/g, " ")
    .replace(/\s+/g, " ")
    .trim();
}

export default function CreateAppModal({
  workflowId,
  workflowName,
  loopType,
  configSchema,
  defaultConfig,
  workflowSnapshot,
  authHeaders,
  onClose,
  onConfigureWorkflow,
}: Props) {
  const [name, setName] = useState(appNameFromWorkflow(workflowName));
  const [description, setDescription] = useState(defaultDescription(workflowName, loopType));
  const [category, setCategory] = useState(loopType || "system");
  const [priceUsd, setPriceUsd] = useState("");
  const [saving, setSaving] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [created, setCreated] = useState<CreateAppResponse["app"] | null>(null);

  const inputSummary = useMemo(() => {
    const fields = configSchema.fields || [];
    if (!fields.length) return "No required run settings defined yet.";
    return fields
      .slice(0, 4)
      .map((field) => field.label || field.key)
      .join(", ");
  }, [configSchema]);

  const hasInputContract = Boolean((configSchema.fields || []).length);
  const canSave = Boolean(workflowId && name.trim() && hasInputContract && !saving);

  const save = async () => {
    if (!workflowId) {
      setError("Select or save a Studio workflow before creating an app.");
      return;
    }
    if (!name.trim()) {
      setError("App name is required.");
      return;
    }
    if (!hasInputContract) {
      setError("Configure workflow settings before creating an app. Product stages use this real input contract.");
      return;
    }
    setSaving(true);
    setError(null);
    setCreated(null);
    try {
      const res = await fetch("/api/studio/user-apps", {
        method: "POST",
        headers: await authHeaders(),
        body: JSON.stringify({
          workflow_id: workflowId,
          workflow_name: workflowName,
          name: name.trim(),
          description: description.trim(),
          category,
          loop_type: loopType,
          price_usd: priceUsd.trim() ? Number(priceUsd) : null,
          input_schema: configSchema,
          default_config: defaultConfig,
          app_config: {
            workflow_snapshot: workflowSnapshot,
            entrypoint: "studio_workflow",
          },
        }),
      });
      const data = (await res.json().catch(() => ({}))) as CreateAppResponse;
      if (!res.ok || data.status !== "ok") {
        throw new Error(data.detail || data.message || "Could not create app.");
      }
      setCreated(data.app || null);
      window.dispatchEvent(new Event("refreshApps"));
    } catch (err) {
      setError(err instanceof Error ? err.message : "Could not create app.");
    } finally {
      setSaving(false);
    }
  };

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 px-4">
      <div className="max-h-[92vh] w-[760px] max-w-[96vw] overflow-y-auto rounded-2xl border border-slate-800 bg-slate-900 p-6 text-slate-100 shadow-2xl scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
        <div className="flex items-start justify-between gap-4">
          <div>
            <h2 className="text-2xl font-bold text-cyan-400">Create App</h2>
            <p className="mt-1 text-sm text-slate-400">
              Package the selected Studio workflow as a private app. Marketplace publishing can be reviewed later by admin.
            </p>
          </div>
          <button onClick={onClose} className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-200 hover:bg-slate-800">
            Close
          </button>
        </div>

        <div className="mt-5 rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm">
          <div className="text-xs font-semibold uppercase text-slate-500">Source Workflow</div>
          <div className="mt-1 text-slate-100">{workflowName || "No workflow selected"}</div>
          <div className="mt-1 break-all text-xs text-slate-500">{workflowId || "Save or select a workflow first"}</div>
        </div>

        <div className="mt-5 grid gap-4 md:grid-cols-2">
          <label className="grid gap-1">
            <span className="text-xs font-semibold uppercase text-slate-400">App Name</span>
            <input
              value={name}
              onChange={(event) => setName(event.target.value)}
              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
            />
          </label>
          <label className="grid gap-1">
            <span className="text-xs font-semibold uppercase text-slate-400">Category</span>
            <select
              value={category}
              onChange={(event) => setCategory(event.target.value)}
              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
            >
              <option value="digital">Digital</option>
              <option value="analog">Analog</option>
              <option value="embedded">Embedded</option>
              <option value="system">System</option>
              <option value="validation">Validation</option>
            </select>
          </label>
          <label className="grid gap-1 md:col-span-2">
            <span className="text-xs font-semibold uppercase text-slate-400">Description</span>
            <textarea
              value={description}
              onChange={(event) => setDescription(event.target.value)}
              rows={4}
              className="resize-none rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
            />
          </label>
          <label className="grid gap-1">
            <span className="text-xs font-semibold uppercase text-slate-400">Marketplace Price USD</span>
            <input
              value={priceUsd}
              onChange={(event) => setPriceUsd(event.target.value.replace(/[^\d.]/g, ""))}
              placeholder="Optional"
              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
            />
          </label>
          <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-3 text-sm text-slate-300">
            <div className="text-xs font-semibold uppercase text-slate-500">Inputs</div>
            <div className="mt-1">{inputSummary}</div>
            {!hasInputContract && (
              <button
                type="button"
                onClick={onConfigureWorkflow}
                className="mt-3 rounded border border-cyan-700 px-3 py-1.5 text-xs font-semibold text-cyan-200 hover:bg-cyan-950/40"
              >
                Configure Workflow Settings
              </button>
            )}
          </div>
        </div>

        {error && (
          <div className="mt-4 rounded-lg border border-red-800 bg-red-950/40 px-3 py-2 text-sm text-red-200">{error}</div>
        )}
        {created && (
          <div className="mt-4 rounded-lg border border-emerald-800 bg-emerald-950/40 px-3 py-2 text-sm text-emerald-200">
            Created private app {created.name || name}. Status: {created.status || "private"}.
          </div>
        )}

        <div className="mt-6 flex justify-end gap-3">
          <button onClick={onClose} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800">
            Cancel
          </button>
          <button
            onClick={save}
            disabled={!canSave}
            className="rounded-lg bg-cyan-500 px-4 py-2 text-sm font-bold text-black hover:bg-cyan-400 disabled:cursor-not-allowed disabled:bg-slate-700 disabled:text-slate-400"
          >
            {saving ? "Creating..." : "Create Private App"}
          </button>
        </div>
      </div>
    </div>
  );
}
