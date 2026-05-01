"use client";

import { useEffect, useState } from "react";
import { useParams } from "next/navigation";
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
  agent_spec?: Record<string, unknown>;
  skills?: string[];
  tools?: string[];
  hooks?: string[];
  reviews?: Review[];
};

type Review = { id?: string; user_id?: string; rating: number; review_text?: string; created_at?: string };

type DetailResponse = { status: string; agent: Listing };

type InstallResponse = { status: string; installed_agent?: { agent_name?: string } };

export default function MarketplaceAgentDetailPage() {
  const params = useParams<{ slug: string }>();
  const slug = params.slug;
  const [agent, setAgent] = useState<Listing | null>(null);
  const [rating, setRating] = useState(5);
  const [reviewText, setReviewText] = useState("");
  const [message, setMessage] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);

  async function loadAgent() {
    setLoading(true);
    setError(null);
    try {
      const data = await apiGet<DetailResponse>(`/marketplace/agents/${slug}`);
      setAgent(data.agent);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Failed to load agent.");
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    if (slug) loadAgent();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [slug]);

  async function installAgent() {
    if (!agent) return;
    setMessage(null);
    setError(null);
    try {
      const data = await apiPost<InstallResponse>(`/marketplace/agents/${agent.id}/install`);
      setMessage(`Installed ${data.installed_agent?.agent_name || agent.name} into My Agents.`);
      window.dispatchEvent(new Event("refreshAgents"));
    } catch (err) {
      setError(err instanceof Error ? err.message : "Install failed.");
    }
  }

  async function submitReview() {
    if (!agent) return;
    setMessage(null);
    setError(null);
    try {
      await apiPost(`/marketplace/agents/${agent.id}/reviews`, { rating, review_text: reviewText });
      setReviewText("");
      setMessage("Review saved.");
      loadAgent();
    } catch (err) {
      setError(err instanceof Error ? err.message : "Review failed.");
    }
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="marketplace" showMarketplace maxWidthClass="max-w-6xl" />

      <section className="mx-auto max-w-6xl px-6 py-8">
        {loading ? <div className="text-slate-400">Loading...</div> : null}
        {error ? <div className="rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-red-200">{error}</div> : null}
        {message ? <div className="rounded-xl border border-emerald-900/70 bg-emerald-950/30 p-4 text-emerald-200">{message}</div> : null}

        {agent ? (
          <div className="grid gap-6 lg:grid-cols-[1fr_360px]">
            <div className="space-y-5">
              <section className="rounded-2xl border border-slate-800 bg-slate-900/35 p-6">
                <div className="flex flex-wrap items-start justify-between gap-4">
                  <div>
                    <div className="text-sm uppercase tracking-wide text-cyan-300">Verified marketplace agent</div>
                    <h1 className="mt-2 text-3xl font-extrabold">{agent.name}</h1>
                    <p className="mt-3 max-w-3xl leading-7 text-slate-300">{agent.description || "No description provided."}</p>
                  </div>
                  <button onClick={installAgent} className="rounded-xl bg-cyan-600 px-5 py-3 font-bold hover:bg-cyan-500">Install Agent</button>
                </div>
                <div className="mt-5 flex flex-wrap gap-2 text-xs text-slate-300">
                  <span className="rounded-full border border-slate-700 px-2 py-1">{agent.loop_type || "system"}</span>
                  <span className="rounded-full border border-slate-700 px-2 py-1">{agent.domain || "general"}</span>
                  <span className="rounded-full border border-slate-700 px-2 py-1">v{agent.version || "1.0.0"}</span>
                </div>
              </section>

              <section className="rounded-2xl border border-slate-800 bg-slate-950/55 p-5">
                <h2 className="font-bold text-cyan-300">AgentSpec</h2>
                <pre className="mt-3 max-h-96 overflow-auto rounded-xl bg-black/40 p-4 text-xs text-slate-200">{JSON.stringify(agent.agent_spec || {}, null, 2)}</pre>
              </section>
            </div>

            <aside className="space-y-5">
              <section className="rounded-2xl border border-slate-800 bg-slate-950/55 p-5">
                <h2 className="font-bold text-cyan-300">Dependencies</h2>
                <div className="mt-3 space-y-3 text-sm text-slate-300">
                  <div><span className="text-slate-500">Skills:</span> {(agent.skills || []).join(", ") || "None"}</div>
                  <div><span className="text-slate-500">Tools:</span> {(agent.tools || []).join(", ") || "None"}</div>
                  <div><span className="text-slate-500">Hooks:</span> {(agent.hooks || []).join(", ") || "None"}</div>
                </div>
              </section>

              <section className="rounded-2xl border border-slate-800 bg-slate-950/55 p-5">
                <h2 className="font-bold text-cyan-300">Reviews</h2>
                <div className="mt-3 space-y-2">
                  {(agent.reviews || []).map((review) => (
                    <div key={review.id || review.user_id} className="rounded-xl border border-slate-800 bg-black/30 p-3 text-sm text-slate-300">
                      <div className="font-semibold text-slate-100">{review.rating}/5</div>
                      <div className="mt-1">{review.review_text || "No comment."}</div>
                    </div>
                  ))}
                  {(agent.reviews || []).length === 0 ? <div className="text-sm text-slate-500">No reviews yet.</div> : null}
                </div>
                <div className="mt-4 space-y-2">
                  <select value={rating} onChange={(event) => setRating(Number(event.target.value))} className="w-full rounded-xl border border-slate-700 bg-black/30 px-3 py-2 text-slate-100">
                    {[5, 4, 3, 2, 1].map((value) => <option key={value} value={value}>{value} stars</option>)}
                  </select>
                  <textarea value={reviewText} onChange={(event) => setReviewText(event.target.value)} placeholder="Optional review" className="h-24 w-full resize-none rounded-xl border border-slate-700 bg-black/30 p-3 text-slate-100" />
                  <button onClick={submitReview} className="w-full rounded-xl border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900">Save review</button>
                </div>
              </section>
            </aside>
          </div>
        ) : null}
      </section>
    </main>
  );
}
