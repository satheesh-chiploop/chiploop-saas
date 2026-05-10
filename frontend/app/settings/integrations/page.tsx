"use client";

import { useEffect, useState } from "react";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type GitHubStatusResponse = {
  status: string;
  github: {
    configured: boolean;
    auth_mode?: string | null;
    connect_url?: string | null;
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

  useEffect(() => {
    apiGet<GitHubStatusResponse>("/settings/github/status")
      .then((data) => setGithub(data.github))
      .catch((err) => setError(errorMessage(err)));
  }, []);

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
          <span className={`rounded-full border px-3 py-1 text-xs ${github?.configured ? "border-emerald-700 bg-emerald-950/40 text-emerald-200" : "border-amber-700 bg-amber-950/30 text-amber-100"}`}>
            {github?.configured ? "Configured" : "Not configured"}
          </span>
        </div>

        {error ? <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">{error}</div> : null}

        <div className="mt-5 rounded-lg border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
          {github?.configured ? (
            <p>Backend GitHub access is available through `{github.auth_mode || "token"}` mode.</p>
          ) : (
            <div className="space-y-2">
              <p>{github?.message || "GitHub is not configured on this deployment."}</p>
              <p className="text-xs text-slate-500">Set `GITHUB_TOKEN` for MVP import support. For production, use a GitHub App installation token.</p>
              {github?.connect_url ? (
                <a href={github.connect_url} className="inline-block rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900">
                  Install GitHub App
                </a>
              ) : null}
            </div>
          )}
        </div>
      </section>
    </SettingsNav>
  );
}
