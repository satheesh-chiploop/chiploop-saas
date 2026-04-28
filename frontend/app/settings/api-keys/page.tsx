"use client";

import { useEffect, useMemo, useState } from "react";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";

type ApiKeyMetadata = {
  id: string;
  key_prefix: string;
  name: string;
  created_at: string;
  last_used_at?: string | null;
  revoked_at?: string | null;
};

type ApiKeyListResponse = {
  status: string;
  api_keys: ApiKeyMetadata[];
};

type ApiKeyCreateResponse = {
  status: string;
  api_key: string;
  api_key_metadata: ApiKeyMetadata;
};

function formatDate(value?: string | null): string {
  if (!value) return "-";
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return value;
  return date.toLocaleString();
}

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Request failed.";
}

export default function ApiKeysPage() {
  const [keys, setKeys] = useState<ApiKeyMetadata[]>([]);
  const [loading, setLoading] = useState(true);
  const [creating, setCreating] = useState(false);
  const [revokingId, setRevokingId] = useState<string | null>(null);
  const [name, setName] = useState("local CLI");
  const [newKey, setNewKey] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [copied, setCopied] = useState(false);

  const activeKeys = useMemo(
    () => keys.filter((key) => !key.revoked_at).length,
    [keys]
  );

  async function loadKeys() {
    setError(null);
    setLoading(true);
    try {
      const data = await apiGet<ApiKeyListResponse>("/settings/api-keys");
      setKeys(data.api_keys || []);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadKeys();
  }, []);

  async function createKey() {
    const trimmed = name.trim();
    if (!trimmed) {
      setError("Enter a key name.");
      return;
    }

    setCreating(true);
    setError(null);
    setCopied(false);
    try {
      const data = await apiPost<ApiKeyCreateResponse>("/settings/api-keys", {
        name: trimmed,
        environment: "test",
      });
      setNewKey(data.api_key);
      await loadKeys();
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setCreating(false);
    }
  }

  async function revokeKey(key: ApiKeyMetadata) {
    const confirmed = window.confirm(`Revoke API key "${key.name}"? This cannot be undone.`);
    if (!confirmed) return;

    setRevokingId(key.id);
    setError(null);
    try {
      await apiPost<{ status: string }>(`/settings/api-keys/${encodeURIComponent(key.id)}/revoke`);
      await loadKeys();
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setRevokingId(null);
    }
  }

  async function copyNewKey() {
    if (!newKey) return;
    await navigator.clipboard.writeText(newKey);
    setCopied(true);
  }

  return (
    <SettingsNav>
      <div className="space-y-6">
        <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
          <div className="flex flex-col gap-4 md:flex-row md:items-end md:justify-between">
            <div>
              <h2 className="text-xl font-bold">API Keys</h2>
              <p className="mt-1 text-sm text-slate-400">
                Use these keys with the ChipLoop SDK and CLI. Active keys: {activeKeys}.
              </p>
            </div>

            <div className="flex w-full flex-col gap-2 sm:w-auto sm:min-w-80 sm:flex-row">
              <input
                value={name}
                onChange={(event) => setName(event.target.value)}
                className="min-w-0 flex-1 rounded-lg border border-slate-700 bg-black/40 px-3 py-2 text-sm text-white outline-none focus:border-cyan-600"
                placeholder="Key name"
              />
              <button
                onClick={createKey}
                disabled={creating}
                className="rounded-lg bg-cyan-700 px-4 py-2 text-sm font-semibold text-white transition hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-400"
              >
                {creating ? "Creating..." : "Create key"}
              </button>
            </div>
          </div>
        </section>

        {newKey ? (
          <section className="rounded-xl border border-amber-600/50 bg-amber-950/20 p-5">
            <div className="flex flex-col gap-4 lg:flex-row lg:items-start lg:justify-between">
              <div className="min-w-0">
                <h3 className="font-bold text-amber-200">Copy this key now</h3>
                <p className="mt-1 text-sm text-amber-100/80">
                  This raw API key will not be shown again after you leave this page.
                </p>
                <code className="mt-3 block overflow-x-auto rounded-lg border border-amber-700/60 bg-black/50 p-3 text-sm text-amber-100">
                  {newKey}
                </code>
              </div>
              <button
                onClick={copyNewKey}
                className="shrink-0 rounded-lg border border-amber-500/60 px-4 py-2 text-sm font-semibold text-amber-100 transition hover:bg-amber-900/40"
              >
                {copied ? "Copied" : "Copy key"}
              </button>
            </div>
          </section>
        ) : null}

        {error ? (
          <div className="rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-sm text-red-200">
            {error}
          </div>
        ) : null}

        <section className="overflow-hidden rounded-xl border border-slate-800 bg-slate-950/60">
          {loading ? (
            <div className="p-6 text-sm text-slate-400">Loading API keys...</div>
          ) : keys.length === 0 ? (
            <div className="p-6 text-sm text-slate-400">No API keys yet.</div>
          ) : (
            <div className="overflow-x-auto">
              <table className="w-full min-w-[760px] text-left text-sm">
                <thead className="border-b border-slate-800 bg-slate-900/80 text-slate-300">
                  <tr>
                    <th className="px-4 py-3 font-semibold">Name</th>
                    <th className="px-4 py-3 font-semibold">Prefix</th>
                    <th className="px-4 py-3 font-semibold">Created</th>
                    <th className="px-4 py-3 font-semibold">Last Used</th>
                    <th className="px-4 py-3 font-semibold">Status</th>
                    <th className="px-4 py-3 font-semibold">Action</th>
                  </tr>
                </thead>
                <tbody className="divide-y divide-slate-800">
                  {keys.map((key) => {
                    const revoked = Boolean(key.revoked_at);
                    return (
                      <tr key={key.id} className="text-slate-200">
                        <td className="px-4 py-3">{key.name || "-"}</td>
                        <td className="px-4 py-3 font-mono text-xs text-cyan-200">
                          {key.key_prefix}
                        </td>
                        <td className="px-4 py-3 text-slate-300">{formatDate(key.created_at)}</td>
                        <td className="px-4 py-3 text-slate-300">{formatDate(key.last_used_at)}</td>
                        <td className="px-4 py-3">
                          <span
                            className={`rounded-full px-2 py-1 text-xs ${
                              revoked
                                ? "border border-slate-700 bg-slate-900 text-slate-400"
                                : "border border-emerald-700/60 bg-emerald-950/40 text-emerald-200"
                            }`}
                          >
                            {revoked ? "Revoked" : "Active"}
                          </span>
                        </td>
                        <td className="px-4 py-3">
                          <button
                            disabled={revoked || revokingId === key.id}
                            onClick={() => revokeKey(key)}
                            className="rounded-lg border border-slate-700 px-3 py-1.5 text-xs text-slate-200 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                          >
                            {revokingId === key.id ? "Revoking..." : "Revoke"}
                          </button>
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>
          )}
        </section>
      </div>
    </SettingsNav>
  );
}
