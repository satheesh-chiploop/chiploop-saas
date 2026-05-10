"use client";

import { useEffect, useState } from "react";
import { useRouter, useSearchParams } from "next/navigation";
import SettingsNav from "../../../SettingsNav";
import { ApiClientError, apiPost } from "@/lib/apiClient";

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) return "Your session expired. Please sign in again.";
  if (error instanceof Error) return error.message;
  return "Could not connect GitHub.";
}

export default function GitHubCallbackPage() {
  const router = useRouter();
  const params = useSearchParams();
  const [message, setMessage] = useState("Connecting GitHub...");
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const installationId = params.get("installation_id");
    if (!installationId) {
      setError("Missing GitHub installation id.");
      return;
    }
    apiPost<{ status: string }>("/settings/github/callback", { installation_id: installationId })
      .then(() => {
        setMessage("GitHub connected. Redirecting...");
        window.setTimeout(() => router.replace("/settings/integrations"), 900);
      })
      .catch((err) => setError(errorMessage(err)));
  }, [params, router]);

  return (
    <SettingsNav>
      <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-6">
        <h2 className="text-xl font-bold">GitHub Connection</h2>
        <p className="mt-2 text-sm text-slate-300">{error || message}</p>
        {error ? (
          <button
            onClick={() => router.push("/settings/integrations")}
            className="mt-4 rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-200 hover:bg-slate-900"
          >
            Back to Integrations
          </button>
        ) : null}
      </section>
    </SettingsNav>
  );
}
