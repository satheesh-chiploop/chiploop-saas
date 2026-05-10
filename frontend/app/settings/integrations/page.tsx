"use client";

import { useEffect, useState } from "react";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";

type GitHubStatusResponse = {
  status: string;
  github: {
    configured: boolean;
    auth_mode?: string | null;
    connect_url?: string | null;
    connected?: boolean;
    installation?: {
      github_installation_id?: string;
      github_account_login?: string;
      github_account_type?: string;
    } | null;
    message?: string | null;
  };
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) return "Your session expired. Please sign in again.";
  if (error instanceof Error) return error.message;
  return "Request failed.";
}

export default function IntegrationsPage() {
  const [github, setGithub] = useState<GitHubStatusResponse["github"] | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [busy, setBusy] = useState(false);

  async function loadStatus() {
    setError(null);
    apiGet<GitHubStatusResponse>("/settings/github/status")
      .then((data) => setGithub(data.github))
      .catch((err) => setError(errorMessage(err)));
  }

  useEffect(() => {
    loadStatus();
  }, []);

  async function disconnect() {
    if (!window.confirm("Disconnect GitHub from this ChipLoop account?")) return;
    setBusy(true);
    setError(null);
    try {
      await apiPost<{ status: string }>("/settings/github/disconnect", {
        installation_id: github?.installation?.github_installation_id,
      });
      await loadStatus();
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setBusy(false);
    }
  }

  return (
    <SettingsNav>
      <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
        <div className="flex flex-col gap-4 md:flex-row md:items-start md:justify-between">
          <div>
            <h2 className="text-xl font-bold">GitHub</h2>
            <p className="mt-1 max-w-2xl text-sm text-slate-400">
              Import repo files into ChipLoop runs and prepare generated outputs for GitHub export or pull requests.
            </p>
          </div>
          <span className={`rounded-full border px-3 py-1 text-xs ${github?.connected ? "border-emerald-700 bg-emerald-950/40 text-emerald-200" : "border-amber-700 bg-amber-950/30 text-amber-100"}`}>
            {github?.connected ? "Connected" : "Not connected"}
          </span>
        </div>

        {error ? <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">{error}</div> : null}

        <div className="mt-5 rounded-lg border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
          {github?.connected ? (
            <div className="flex flex-col gap-4 md:flex-row md:items-center md:justify-between">
              <div>
                <p>
                  Connected to GitHub account{" "}
                  <span className="font-semibold text-slate-100">{github.installation?.github_account_login || "GitHub"}</span>.
                </p>
                <p className="mt-1 text-xs text-slate-500">Access mode: {github.auth_mode || "github_app"}</p>
              </div>
              <button
                onClick={disconnect}
                disabled={busy}
                className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
              >
                {busy ? "Disconnecting..." : "Disconnect"}
              </button>
            </div>
          ) : (
            <div className="space-y-2">
              <p>{github?.message || "Connect GitHub to import files from your repositories."}</p>
              <p className="text-xs text-slate-500">You choose which personal or organization repositories ChipLoop can access.</p>
              {github?.connect_url ? (
                <a href={github.connect_url} className="inline-block rounded-lg bg-cyan-700 px-3 py-2 text-xs font-semibold text-white hover:bg-cyan-600">
                  Connect GitHub
                </a>
              ) : (
                <p className="text-xs text-amber-100">GitHub App is not configured by the platform yet.</p>
              )}
            </div>
          )}
        </div>
      </section>

      <section className="mt-6 rounded-xl border border-slate-800 bg-slate-950/60 p-5">
        <div className="flex flex-col gap-4 md:flex-row md:items-start md:justify-between">
          <div>
            <h2 className="text-xl font-bold">Cursor and VS Code</h2>
            <p className="mt-1 max-w-2xl text-sm text-slate-400">
              Use ChipLoop from your IDE through the SDK/CLI and an API key. Cursor works through the integrated terminal; VS Code uses the same CLI path and the command-palette extension scaffold.
            </p>
          </div>
          <span className="rounded-full border border-cyan-800 bg-cyan-950/30 px-3 py-1 text-xs text-cyan-100">
            Developer
          </span>
        </div>

        <div className="mt-5 grid gap-4 lg:grid-cols-2">
          <div className="rounded-lg border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
            <h3 className="font-semibold text-slate-100">Cursor flow</h3>
            <ol className="mt-3 space-y-2">
              <li>Create an API key in Settings, API Keys.</li>
              <li>Open the Cursor terminal and install the ChipLoop SDK/CLI.</li>
              <li>Set `CHIPLOOP_BASE_URL` and `CHIPLOOP_API_KEY` in your shell.</li>
              <li>Run ChipLoop against a local spec file and download artifacts for review.</li>
            </ol>
          </div>

          <div className="rounded-lg border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
            <h3 className="font-semibold text-slate-100">VS Code flow</h3>
            <ol className="mt-3 space-y-2">
              <li>Use `ChipLoop: Configure` to set the base URL and API key.</li>
              <li>Run `ChipLoop: Run Workflow from Current File` or `ChipLoop: Run Arch2RTL`.</li>
              <li>Check workflow status and download generated artifacts into the workspace.</li>
              <li>Review RTL, SDC, UPF, and reports before committing changes.</li>
            </ol>
          </div>
        </div>

        <div className="mt-4 flex flex-wrap gap-2">
          <a href="/settings/api-keys" className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-semibold text-cyan-200 hover:bg-slate-900">
            Create API key
          </a>
          <a href="/help?topic=cursor-vscode" className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-semibold text-cyan-200 hover:bg-slate-900">
            View IDE guide
          </a>
        </div>
      </section>
    </SettingsNav>
  );
}
