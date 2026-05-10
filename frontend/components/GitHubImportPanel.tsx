"use client";

import { useEffect, useState } from "react";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";

type GitHubStatusResponse = {
  status: string;
  github: {
    configured: boolean;
    connected?: boolean;
    connect_url?: string | null;
    message?: string | null;
  };
};

type GitHubImportResponse = {
  status: string;
  source: { owner: string; repo: string; ref: string };
  files: Array<{ path: string; content: string; size?: number }>;
  combined_text: string;
};

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 503) return "GitHub is not configured on this deployment.";
  if (error instanceof ApiClientError && error.status === 401) return "Sign in again to import from GitHub.";
  if (error instanceof Error) return error.message;
  return "GitHub import failed.";
}

export default function GitHubImportPanel({
  onImport,
  compact = false,
}: {
  onImport: (text: string, files: GitHubImportResponse["files"], source: GitHubImportResponse["source"]) => void;
  compact?: boolean;
}) {
  const [configured, setConfigured] = useState<boolean | null>(null);
  const [connectUrl, setConnectUrl] = useState<string | null>(null);
  const [owner, setOwner] = useState("");
  const [repo, setRepo] = useState("");
  const [ref, setRef] = useState("main");
  const [paths, setPaths] = useState("");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [imported, setImported] = useState<string | null>(null);

  useEffect(() => {
    apiGet<GitHubStatusResponse>("/settings/github/status")
      .then((data) => {
        setConfigured(Boolean(data.github?.configured));
        setConnectUrl(data.github?.connect_url || null);
      })
      .catch(() => setConfigured(false));
  }, []);

  async function importFiles() {
    const selectedPaths = paths
      .split(/[\n,]+/)
      .map((item) => item.trim())
      .filter(Boolean);
    if (!owner.trim() || !repo.trim() || selectedPaths.length === 0) {
      setError("Enter owner, repo, and at least one file path.");
      return;
    }
    setLoading(true);
    setError(null);
    setImported(null);
    try {
      const data = await apiPost<GitHubImportResponse>("/github/import", {
        owner: owner.trim(),
        repo: repo.trim(),
        ref: ref.trim() || "main",
        paths: selectedPaths,
      });
      onImport(data.combined_text, data.files || [], data.source);
      setImported(`${data.files.length} file${data.files.length === 1 ? "" : "s"} imported`);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  return (
    <section className={`rounded-lg border border-slate-800 bg-black/30 ${compact ? "p-3" : "p-4"}`}>
      <div className="flex flex-wrap items-start justify-between gap-3">
        <div>
          <h3 className="text-sm font-bold text-cyan-300">Import from GitHub</h3>
          <p className="mt-1 text-xs text-slate-400">Bring repo files into this ChipLoop run input.</p>
        </div>
        {configured === false && connectUrl ? (
          <a href={connectUrl} className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-200 hover:bg-slate-900">
            Connect
          </a>
        ) : null}
      </div>

      {configured === false ? (
        <div className="mt-3 rounded-md border border-amber-800/60 bg-amber-950/20 p-2 text-xs text-amber-100">
          Connect GitHub in Settings to import files from your repositories.
        </div>
      ) : null}

      <div className="mt-3 grid gap-2 sm:grid-cols-3">
        <input value={owner} onChange={(event) => setOwner(event.target.value)} placeholder="owner/org" className="rounded-md border border-slate-700 bg-slate-950 px-2 py-2 text-xs outline-none focus:border-cyan-600" />
        <input value={repo} onChange={(event) => setRepo(event.target.value)} placeholder="repo" className="rounded-md border border-slate-700 bg-slate-950 px-2 py-2 text-xs outline-none focus:border-cyan-600" />
        <input value={ref} onChange={(event) => setRef(event.target.value)} placeholder="branch" className="rounded-md border border-slate-700 bg-slate-950 px-2 py-2 text-xs outline-none focus:border-cyan-600" />
      </div>
      <textarea
        value={paths}
        onChange={(event) => setPaths(event.target.value)}
        placeholder="rtl/top.sv&#10;constraints/top.sdc&#10;specs/design.md"
        className="mt-2 h-20 w-full resize-none rounded-md border border-slate-700 bg-slate-950 p-2 text-xs outline-none focus:border-cyan-600"
      />
      <div className="mt-2 flex items-center justify-between gap-3">
        <div className="text-xs text-slate-400">{imported || error || ""}</div>
        <button
          type="button"
          onClick={importFiles}
          disabled={loading || configured === false}
          className="rounded-md bg-cyan-700 px-3 py-1.5 text-xs font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
        >
          {loading ? "Importing..." : "Import"}
        </button>
      </div>
    </section>
  );
}
