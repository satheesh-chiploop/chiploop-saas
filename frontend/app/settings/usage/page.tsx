"use client";

import { useEffect, useState } from "react";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type UsageEvent = {
  user_id?: string;
  api_key_id?: string;
  endpoint?: string;
  event_type?: string;
  workflow_id?: string | null;
  created_at?: string;
};

type UsageSummary = {
  user_id?: string;
  recent_event_count?: number;
  by_event_type?: Record<string, number>;
  recent_events?: UsageEvent[];
};

type UsageResponse = {
  status: string;
  usage: UsageSummary;
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
  return "Failed to load usage.";
}

export default function UsagePage() {
  const [usage, setUsage] = useState<UsageSummary | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  async function loadUsage() {
    setLoading(true);
    setError(null);
    try {
      const data = await apiGet<UsageResponse>("/settings/usage");
      setUsage(data.usage || {});
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadUsage();
  }, []);

  const byType = usage?.by_event_type || {};
  const recentEvents = usage?.recent_events || [];

  return (
    <SettingsNav>
      <div className="space-y-6">
        <section className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
          <div className="flex flex-col gap-4 md:flex-row md:items-center md:justify-between">
            <div>
              <h2 className="text-xl font-bold">Usage</h2>
              <p className="mt-1 text-sm text-slate-400">
                SDK and CLI activity for your account. Billing is not shown here.
              </p>
            </div>
            <button
              onClick={loadUsage}
              disabled={loading}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
            >
              {loading ? "Refreshing..." : "Refresh"}
            </button>
          </div>
        </section>

        {error ? (
          <div className="rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-sm text-red-200">
            {error}
          </div>
        ) : null}

        {loading ? (
          <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-6 text-sm text-slate-400">
            Loading usage...
          </div>
        ) : (
          <>
            <section className="grid gap-4 md:grid-cols-3">
              <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Recent events</div>
                <div className="mt-2 text-3xl font-extrabold text-cyan-200">
                  {usage?.recent_event_count ?? recentEvents.length}
                </div>
              </div>

              {Object.keys(byType).length === 0 ? (
                <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5 md:col-span-2">
                  <div className="text-sm text-slate-400">No event breakdown yet.</div>
                </div>
              ) : (
                <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-5 md:col-span-2">
                  <div className="text-sm font-semibold text-slate-200">Event types</div>
                  <div className="mt-3 flex flex-wrap gap-2">
                    {Object.entries(byType).map(([eventType, count]) => (
                      <span
                        key={eventType}
                        className="rounded-full border border-slate-700 bg-slate-900 px-3 py-1 text-xs text-slate-200"
                      >
                        {eventType}: {count}
                      </span>
                    ))}
                  </div>
                </div>
              )}
            </section>

            <section className="overflow-hidden rounded-xl border border-slate-800 bg-slate-950/60">
              {recentEvents.length === 0 ? (
                <div className="p-6 text-sm text-slate-400">No usage events yet.</div>
              ) : (
                <div className="overflow-x-auto">
                  <table className="w-full min-w-[760px] text-left text-sm">
                    <thead className="border-b border-slate-800 bg-slate-900/80 text-slate-300">
                      <tr>
                        <th className="px-4 py-3 font-semibold">Event Type</th>
                        <th className="px-4 py-3 font-semibold">Endpoint</th>
                        <th className="px-4 py-3 font-semibold">Workflow</th>
                        <th className="px-4 py-3 font-semibold">Created</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-slate-800">
                      {recentEvents.map((event, index) => (
                        <tr key={`${event.created_at || "event"}-${index}`} className="text-slate-200">
                          <td className="px-4 py-3">{event.event_type || "-"}</td>
                          <td className="px-4 py-3 font-mono text-xs text-cyan-200">
                            {event.endpoint || "-"}
                          </td>
                          <td className="px-4 py-3 text-slate-300">{event.workflow_id || "-"}</td>
                          <td className="px-4 py-3 text-slate-300">{formatDate(event.created_at)}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              )}
            </section>
          </>
        )}
      </div>
    </SettingsNav>
  );
}
