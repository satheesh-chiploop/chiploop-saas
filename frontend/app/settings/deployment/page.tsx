"use client";

import { useEffect, useMemo, useState } from "react";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";

type DeploymentMode = {
  mode: string;
  label: string;
  frontend_owner: string;
  backend_owner: string;
  data_owner: string;
  tool_owner: string;
  model_owner: string;
  description: string;
  capabilities: string[];
};

type ToolEntry = {
  configured: string;
  resolved: string;
  available: boolean;
};

type Adapter = {
  adapter_id: string;
  capability: string;
  tool: string;
  description: string;
  expected_outputs?: string[];
};

type DeploymentResponse = {
  status: string;
  editable: boolean;
  deployment: {
    active: DeploymentMode;
    available_modes: DeploymentMode[];
    env: Record<string, string>;
  };
  model_profile: {
    model_profile_id: string;
    provider: string;
    ai_billing_mode?: string;
    model_key_owner?: string;
    capabilities: string[];
    agents: string[];
  };
  tool_profile: {
    profile_id: string;
    runner: string;
    artifact_policy: string;
    tools: Record<string, ToolEntry>;
    runtime: Record<string, ToolEntry>;
    env_keys: string[];
  };
  tool_adapters: Adapter[];
  platform_services: Record<string, { provider: string; configured: boolean }>;
  license: {
    mode: string;
    managed_by_chiploop: boolean;
    license_key_configured: boolean;
    third_party_tool_licenses: string;
  };
};

type DiagnosticEntry = {
  status: string;
  available: boolean;
  executable: string;
  returncode?: number | null;
  output: string;
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) return "Your session expired. Please sign in again.";
  if (error instanceof Error) return error.message;
  return "Request failed.";
}

function ownerLabel(value: string): string {
  return value.replaceAll("_", " ");
}

function StatusDot({ ok }: { ok: boolean }) {
  return <span className={`h-2.5 w-2.5 rounded-full ${ok ? "bg-emerald-400" : "bg-amber-400"}`} />;
}

function ToolTable({ title, entries }: { title: string; entries: Record<string, ToolEntry> }) {
  const rows = Object.entries(entries || {});
  return (
    <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
      <div className="flex items-center justify-between gap-3">
        <h2 className="text-lg font-bold">{title}</h2>
        <span className="text-xs text-slate-500">{rows.filter(([, entry]) => entry.available).length}/{rows.length} available</span>
      </div>
      <div className="mt-4 overflow-x-auto">
        <table className="w-full min-w-[680px] text-left text-sm">
          <thead className="text-xs uppercase text-slate-500">
            <tr>
              <th className="border-b border-slate-800 py-2 pr-4">Name</th>
              <th className="border-b border-slate-800 py-2 pr-4">Status</th>
              <th className="border-b border-slate-800 py-2 pr-4">Resolved Path</th>
              <th className="border-b border-slate-800 py-2">Configured</th>
            </tr>
          </thead>
          <tbody>
            {rows.map(([name, entry]) => (
              <tr key={name} className="border-b border-slate-900/80">
                <td className="py-2 pr-4 font-mono text-xs text-slate-200">{name}</td>
                <td className="py-2 pr-4">
                  <span className="inline-flex items-center gap-2 rounded-md border border-slate-800 px-2 py-1 text-xs text-slate-300">
                    <StatusDot ok={entry.available} />
                    {entry.available ? "available" : "missing"}
                  </span>
                </td>
                <td className="max-w-[320px] truncate py-2 pr-4 font-mono text-xs text-slate-400" title={entry.resolved || ""}>
                  {entry.resolved || "-"}
                </td>
                <td className="max-w-[320px] truncate py-2 font-mono text-xs text-slate-500" title={entry.configured || ""}>
                  {entry.configured || "-"}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}

export default function DeploymentSettingsPage() {
  const [data, setData] = useState<DeploymentResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [diagnostics, setDiagnostics] = useState<Record<string, DiagnosticEntry> | null>(null);
  const [diagnosticsBusy, setDiagnosticsBusy] = useState(false);
  const [modelCheck, setModelCheck] = useState<string | null>(null);
  const [modelCheckBusy, setModelCheckBusy] = useState(false);

  useEffect(() => {
    apiGet<DeploymentResponse>("/settings/deployment")
      .then((response) => setData(response))
      .catch((err) => setError(errorMessage(err)));
  }, []);

  const active = data?.deployment.active;
  const adapterGroups = useMemo(() => {
    const groups: Record<string, Adapter[]> = {};
    for (const adapter of data?.tool_adapters || []) {
      groups[adapter.capability] = groups[adapter.capability] || [];
      groups[adapter.capability].push(adapter);
    }
    return groups;
  }, [data]);

  async function runDiagnostics() {
    setDiagnosticsBusy(true);
    setError(null);
    try {
      const response = await apiPost<{ status: string; diagnostics: { results: Record<string, DiagnosticEntry> } }>(
        "/settings/deployment/tool-diagnostics",
        {},
      );
      setDiagnostics(response.diagnostics.results);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setDiagnosticsBusy(false);
    }
  }

  async function runModelCheck() {
    setModelCheckBusy(true);
    setError(null);
    try {
      const response = await apiPost<{ status: string; response: string }>("/settings/deployment/model-diagnostics", {});
      setModelCheck(response.response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setModelCheckBusy(false);
    }
  }

  async function downloadSupportBundle() {
    setError(null);
    try {
      const response = await apiGet<{ status: string; support_bundle: unknown }>("/settings/deployment/support-bundle");
      const blob = new Blob([JSON.stringify(response.support_bundle, null, 2)], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      const anchor = document.createElement("a");
      anchor.href = url;
      anchor.download = "chiploop_support_bundle.json";
      anchor.click();
      URL.revokeObjectURL(url);
    } catch (err) {
      setError(errorMessage(err));
    }
  }

  return (
    <SettingsNav>
      {error ? <div className="mb-5 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">{error}</div> : null}
      {!data ? <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5 text-sm text-slate-400">Loading deployment status...</div> : null}
      {data && active ? (
        <div className="space-y-6">
          <section className="rounded-xl border border-cyan-900/60 bg-slate-950/70 p-5">
            <div className="flex flex-col gap-4 lg:flex-row lg:items-start lg:justify-between">
              <div>
                <div className="text-xs font-semibold uppercase text-cyan-300">Active deployment mode</div>
                <h2 className="mt-1 text-2xl font-bold">{active.label}</h2>
                <p className="mt-2 max-w-3xl text-sm text-slate-400">{active.description}</p>
              </div>
              <span className="rounded-md border border-slate-700 bg-black/30 px-3 py-2 font-mono text-xs text-slate-300">{active.mode}</span>
            </div>
            <div className="mt-5 grid gap-3 md:grid-cols-5">
              {[
                ["Frontend", active.frontend_owner],
                ["Backend", active.backend_owner],
                ["Data", active.data_owner],
                ["Tools", active.tool_owner],
                ["Models", active.model_owner],
              ].map(([label, value]) => (
                <div key={label} className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">{label}</div>
                  <div className="mt-1 text-sm font-semibold capitalize text-slate-100">{ownerLabel(value)}</div>
                </div>
              ))}
            </div>
          </section>

          <section className="grid gap-5 lg:grid-cols-2">
            <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
              <div className="flex items-start justify-between gap-3">
                <h2 className="text-lg font-bold">Model Profile</h2>
                <button
                  onClick={runModelCheck}
                  disabled={!data.editable || modelCheckBusy}
                  className="rounded-md border border-slate-700 px-3 py-2 text-xs font-semibold text-cyan-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-600"
                >
                  {modelCheckBusy ? "Testing..." : "Test Model"}
                </button>
              </div>
              <div className="mt-4 grid gap-3 sm:grid-cols-2">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Profile</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.model_profile.model_profile_id}</div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Provider</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.model_profile.provider}</div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">AI Billing</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.model_profile.ai_billing_mode || "byok"}</div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Model Keys</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.model_profile.model_key_owner || "customer"}</div>
                </div>
              </div>
              <div className="mt-4 flex flex-wrap gap-2">
                {data.model_profile.capabilities.map((cap) => (
                  <span key={cap} className="rounded-md border border-slate-800 px-2 py-1 font-mono text-xs text-slate-300">{cap}</span>
                ))}
              </div>
              {modelCheck ? <div className="mt-4 rounded-md border border-emerald-900 bg-emerald-950/20 p-3 font-mono text-xs text-emerald-200">{modelCheck}</div> : null}
            </div>

            <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
              <h2 className="text-lg font-bold">Tool Profile</h2>
              <div className="mt-4 grid gap-3 sm:grid-cols-3">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Profile</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.tool_profile.profile_id}</div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Execution</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.tool_profile.runner}</div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">Artifacts</div>
                  <div className="mt-1 font-mono text-sm text-slate-100">{data.tool_profile.artifact_policy}</div>
                </div>
              </div>
              <div className="mt-4 text-xs text-slate-500">Environment keys: {data.tool_profile.env_keys.join(", ") || "none"}</div>
            </div>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
            <h2 className="text-lg font-bold">Platform Services</h2>
            <div className="mt-4 grid gap-3 md:grid-cols-3">
              {Object.entries(data.platform_services || {}).map(([name, service]) => (
                <div key={name} className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="flex items-center justify-between gap-3">
                    <span className="text-xs uppercase text-slate-500">{name}</span>
                    <StatusDot ok={service.configured} />
                  </div>
                  <div className="mt-2 font-mono text-sm text-slate-100">{service.provider}</div>
                </div>
              ))}
            </div>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
            <h2 className="text-lg font-bold">License Status</h2>
            <div className="mt-4 grid gap-3 md:grid-cols-3">
              {[
                ["ChipLoop license mode", data.license.mode],
                ["ChipLoop license", data.license.license_key_configured ? "configured" : "missing"],
                ["Third-party tools", ownerLabel(data.license.third_party_tool_licenses)],
              ].map(([label, value]) => (
                <div key={label} className="rounded-lg border border-slate-800 bg-black/30 p-3">
                  <div className="text-xs text-slate-500">{label}</div>
                  <div className="mt-1 text-sm font-semibold text-slate-100">{value}</div>
                </div>
              ))}
            </div>
          </section>

          <ToolTable title="Runtime" entries={data.tool_profile.runtime} />
          <ToolTable title="Tools" entries={data.tool_profile.tools} />

          <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
            <div className="flex flex-col gap-3 md:flex-row md:items-start md:justify-between">
              <div>
                <h2 className="text-lg font-bold">Tool Diagnostics</h2>
                <p className="mt-1 text-sm text-slate-400">Run version probes using the active tool profile and backend execution environment.</p>
              </div>
              <button
                onClick={runDiagnostics}
                disabled={diagnosticsBusy}
                className="rounded-md bg-cyan-700 px-3 py-2 text-xs font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
              >
                {diagnosticsBusy ? "Running..." : "Run Diagnostics"}
              </button>
            </div>
            {diagnostics ? (
              <div className="mt-4 grid gap-3 lg:grid-cols-2">
                {Object.entries(diagnostics).map(([name, entry]) => (
                  <div key={name} className="rounded-lg border border-slate-800 bg-black/30 p-3">
                    <div className="flex items-center justify-between gap-3">
                      <span className="font-mono text-xs text-slate-100">{name}</span>
                      <span className="inline-flex items-center gap-2 text-xs text-slate-400">
                        <StatusDot ok={entry.available} />
                        {entry.status}
                      </span>
                    </div>
                    <div className="mt-2 truncate font-mono text-[11px] text-slate-500" title={entry.executable}>{entry.executable || "-"}</div>
                    <pre className="mt-2 max-h-24 overflow-auto whitespace-pre-wrap text-[11px] text-slate-400">{entry.output || "No output"}</pre>
                  </div>
                ))}
              </div>
            ) : null}
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
            <div className="flex flex-col gap-3 md:flex-row md:items-center md:justify-between">
              <div>
                <h2 className="text-lg font-bold">Support Bundle</h2>
                <p className="mt-1 text-sm text-slate-400">Download deployment metadata, model profile summary, artifact policy, and tool diagnostics without design artifacts or API keys.</p>
              </div>
              <button
                onClick={downloadSupportBundle}
                disabled={!data.editable}
                className="rounded-md border border-slate-700 px-3 py-2 text-xs font-semibold text-cyan-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-600"
              >
                Download Support Bundle
              </button>
            </div>
          </section>

          <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
            <h2 className="text-lg font-bold">Tool Adapter Registry</h2>
            <div className="mt-4 grid gap-4 lg:grid-cols-2">
              {Object.entries(adapterGroups).map(([capability, adapters]) => (
                <div key={capability} className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="mb-3 font-mono text-xs uppercase text-cyan-300">{capability}</div>
                  <div className="space-y-3">
                    {adapters.map((adapter) => (
                      <div key={adapter.adapter_id} className="rounded-md border border-slate-900 bg-slate-950/70 p-3">
                        <div className="flex flex-wrap items-center justify-between gap-2">
                          <span className="font-mono text-xs text-slate-100">{adapter.adapter_id}</span>
                          <span className="rounded border border-slate-800 px-2 py-1 font-mono text-[11px] text-slate-400">{adapter.tool}</span>
                        </div>
                        <p className="mt-2 text-xs text-slate-400">{adapter.description}</p>
                      </div>
                    ))}
                  </div>
                </div>
              ))}
            </div>
          </section>
        </div>
      ) : null}
    </SettingsNav>
  );
}
