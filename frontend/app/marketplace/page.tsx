"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { apiGet } from "@/lib/apiClient";
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

type MarketplaceResponse = { status: string; agents: Listing[] };

const LOOPS = ["", "digital", "analog", "embedded", "system", "validation"];

export default function MarketplacePage() {
  const router = useRouter();
  const [agents, setAgents] = useState<Listing[]>([]);
  const [query, setQuery] = useState("");
  const [loopType, setLoopType] = useState("");
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
      const data = await apiGet<MarketplaceResponse>(`/marketplace/agents${suffix}`);
      setAgents(data.agents || []);
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

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="marketplace" showMarketplace maxWidthClass="max-w-6xl" />

      <section className="mx-auto max-w-6xl px-6 py-8">
        <div className="rounded-2xl border border-slate-800 bg-slate-900/35 p-6">
          <div className="text-sm uppercase tracking-wide text-cyan-300">Agent ecosystem</div>
          <h1 className="mt-2 text-3xl font-extrabold">Install reviewed agents into your workspace.</h1>
          <p className="mt-2 max-w-3xl text-slate-300">Marketplace agents are approved, versioned metadata packages. Installing creates a private workspace copy under My Agents.</p>
          <div className="mt-5 grid gap-3 md:grid-cols-[1fr_180px_120px]">
            <input value={query} onChange={(e) => setQuery(e.target.value)} onKeyDown={(e) => { if (e.key === "Enter") loadAgents(); }} placeholder="Search agents, skills, tools..." className="rounded-xl border border-slate-700 bg-black/30 px-4 py-3 text-slate-100 outline-none focus:border-cyan-600" />
            <select value={loopType} onChange={(e) => setLoopType(e.target.value)} className="rounded-xl border border-slate-700 bg-black/30 px-4 py-3 text-slate-100 outline-none focus:border-cyan-600">
              {LOOPS.map((loop) => <option key={loop || "all"} value={loop}>{loop ? `${loop[0].toUpperCase()}${loop.slice(1)}` : "All loops"}</option>)}
            </select>
            <button onClick={loadAgents} className="rounded-xl bg-cyan-600 px-4 py-3 font-bold hover:bg-cyan-500">Search</button>
          </div>
        </div>

        {error ? <div className="mt-5 rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-red-200">{error}</div> : null}
        {loading ? <div className="mt-6 text-slate-400">Loading marketplace...</div> : null}

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
