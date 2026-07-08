"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { apiGet, apiPost } from "@/lib/apiClient";
import TopNav from "@/components/TopNav";

type Listing = {
  id: string;
  name: string;
  slug: string;
  description?: string;
  domain?: string;
  loop_type?: string;
  version?: string;
  install_count?: number;
  average_rating?: number;
  review_count?: number;
  skills?: string[];
  tools?: string[];
};

type MarketplaceApp = {
  id: string;
  name: string;
  slug: string;
  description?: string;
  category?: string;
  loop_type?: string;
  workflow_name?: string;
  version?: string;
  install_count?: number;
  review_count?: number;
  price_usd?: number | null;
};

type MarketplaceResponse = { status: string; agents: Listing[] };
type MarketplaceAppsResponse = { status: string; apps: MarketplaceApp[] };

const LOOPS = ["", "digital", "analog", "embedded", "system", "validation"];

export default function MarketplacePage() {
  const router = useRouter();
  const [agents, setAgents] = useState<Listing[]>([]);
  const [apps, setApps] = useState<MarketplaceApp[]>([]);
  const [query, setQuery] = useState("");
  const [loopType, setLoopType] = useState("");
  const [installing, setInstalling] = useState<string | null>(null);
  const [message, setMessage] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  async function loadAgents() {
    setLoading(true);
    setError(null);
    try {
      const params = new URLSearchParams();
      if (query.trim()) params.set("q", query.trim());
      if (loopType) params.set("loop_type", loopType);
      const suffix = params.toString() ? `?${params.toString()}` : "";
      const [agentData, appData] = await Promise.all([
        apiGet<MarketplaceResponse>(`/marketplace/agents${suffix}`),
        apiGet<MarketplaceAppsResponse>(`/marketplace/apps${suffix}`),
      ]);
      setAgents(agentData.agents || []);
      setApps(appData.apps || []);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Failed to load marketplace.");
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadAgents();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [loopType]);

  const filtered = useMemo(() => agents, [agents]);

  async function installApp(app: MarketplaceApp) {
    setInstalling(app.id);
    setMessage(null);
    setError(null);
    try {
      await apiPost(`/marketplace/apps/${app.id}/install`);
      setMessage(`Installed ${app.name} into My Apps.`);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Install app failed.");
    } finally {
      setInstalling(null);
    }
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="marketplace" showMarketplace />

      <section className="mx-auto max-w-[1440px] px-6 py-8">
        <div className="rounded-2xl border border-slate-800 bg-slate-900/35 p-6">
          <div className="text-xs font-semibold uppercase text-cyan-300">Marketplace ecosystem</div>
          <h1 className="mt-2 text-4xl font-extrabold leading-tight text-white sm:text-5xl">Install reviewed agents and apps into your workspace.</h1>
          <p className="mt-2 max-w-3xl text-slate-300">Approved agents install into My Agents. Approved apps install into My Apps as private editable copies.</p>
          <div className="mt-5 grid gap-3 md:grid-cols-[1fr_180px_120px]">
            <input value={query} onChange={(e) => setQuery(e.target.value)} onKeyDown={(e) => { if (e.key === "Enter") loadAgents(); }} placeholder="Search agents, apps, workflows..." className="rounded-xl border border-slate-700 bg-black/30 px-4 py-3 text-slate-100 outline-none focus:border-cyan-600" />
            <select value={loopType} onChange={(e) => setLoopType(e.target.value)} className="rounded-xl border border-slate-700 bg-black/30 px-4 py-3 text-slate-100 outline-none focus:border-cyan-600">
              {LOOPS.map((loop) => <option key={loop || "all"} value={loop}>{loop ? `${loop[0].toUpperCase()}${loop.slice(1)}` : "All loops"}</option>)}
            </select>
            <button onClick={loadAgents} className="rounded-xl bg-cyan-600 px-4 py-3 font-bold hover:bg-cyan-500">Search</button>
          </div>
        </div>

        {error ? <div className="mt-5 rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-red-200">{error}</div> : null}
        {message ? <div className="mt-5 rounded-xl border border-emerald-900/70 bg-emerald-950/30 p-4 text-emerald-200">{message}</div> : null}
        {loading ? <div className="mt-6 text-slate-400">Loading marketplace...</div> : null}

        {!loading && apps.length > 0 ? (
          <section className="mt-6">
            <h2 className="text-xl font-bold text-white">Apps</h2>
            <div className="mt-3 grid gap-4 md:grid-cols-2">
              {apps.map((app) => (
                <div key={app.id} className="rounded-2xl border border-cyan-900/40 bg-slate-950/55 p-5">
                  <div className="flex items-start justify-between gap-3">
                    <div>
                      <h3 className="text-xl font-bold text-slate-100">{app.name}</h3>
                      <p className="mt-2 text-sm leading-6 text-slate-300">{app.description || "No description provided."}</p>
                    </div>
                    <span className="rounded-full border border-cyan-800 bg-cyan-950/40 px-2 py-1 text-xs text-cyan-100">App</span>
                  </div>
                  <div className="mt-4 flex flex-wrap gap-2 text-xs text-slate-300">
                    <span className="rounded-full border border-slate-700 px-2 py-1">{app.loop_type || app.category || "system"}</span>
                    <span className="rounded-full border border-slate-700 px-2 py-1">{app.workflow_name || "Workflow app"}</span>
                    <span className="rounded-full border border-slate-700 px-2 py-1">v{app.version || "1.0.0"}</span>
                  </div>
                  <button
                    onClick={() => installApp(app)}
                    disabled={installing === app.id}
                    className="mt-5 rounded-xl bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
                  >
                    {installing === app.id ? "Installing..." : "Install App"}
                  </button>
                </div>
              ))}
            </div>
          </section>
        ) : null}

        <div className="mt-6 grid gap-4 md:grid-cols-2">
          {filtered.map((agent) => (
            <button key={agent.id} onClick={() => router.push(`/marketplace/agents/${agent.slug || agent.id}`)} className="rounded-2xl border border-slate-800 bg-slate-950/55 p-5 text-left transition hover:border-cyan-700 hover:bg-slate-950">
              <div className="flex items-start justify-between gap-3">
                <div>
                  <h2 className="text-xl font-bold text-slate-100">{agent.name}</h2>
                  <p className="mt-2 text-sm leading-6 text-slate-300">{agent.description || "No description provided."}</p>
                </div>
                <span className="rounded-full border border-emerald-800 bg-emerald-950/40 px-2 py-1 text-xs text-emerald-100">Verified</span>
              </div>
              <div className="mt-4 flex flex-wrap gap-2 text-xs text-slate-300">
                <span className="rounded-full border border-slate-700 px-2 py-1">{agent.loop_type || "system"}</span>
                <span className="rounded-full border border-slate-700 px-2 py-1">v{agent.version || "1.0.0"}</span>
                <span className="rounded-full border border-slate-700 px-2 py-1">{agent.review_count || 0} reviews</span>
              </div>
            </button>
          ))}
        </div>

        {!loading && filtered.length === 0 ? <div className="mt-6 rounded-xl border border-slate-800 bg-black/30 p-6 text-slate-400">No marketplace agents found.</div> : null}
      </section>
    </main>
  );
}
