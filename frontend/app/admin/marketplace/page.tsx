"use client";

import { useEffect, useState } from "react";
import { apiGet, apiPost } from "@/lib/apiClient";
import TopNav from "@/components/TopNav";

type Submission = {
  id?: string;
  submission_id?: string;
  agent_id?: string;
  submitted_by?: string;
  status?: string;
  agent_json?: Record<string, unknown>;
  workflow_json?: Record<string, unknown>;
  review_notes?: string;
  created_at?: string;
};

type SubmissionsResponse = { status: string; submissions: Submission[] };

function submissionId(item: Submission): string {
  return String(item.id || item.submission_id || "");
}

function submissionKind(item: Submission): "App" | "Agent" {
  return item.workflow_json ? "App" : "Agent";
}

function submissionName(item: Submission): string {
  const app = item.workflow_json || {};
  if (item.workflow_json) return String(app.name || app.workflow_name || "Unnamed app");
  const agent = item.agent_json || {};
  return String(agent.agent_name || agent.name || "Unnamed agent");
}

export default function AdminMarketplacePage() {
  const [submissions, setSubmissions] = useState<Submission[]>([]);
  const [selected, setSelected] = useState<Submission | null>(null);
  const [notes, setNotes] = useState("");
  const [loading, setLoading] = useState(true);
  const [message, setMessage] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);

  async function loadSubmissions() {
    setLoading(true);
    setError(null);
    try {
      const data = await apiGet<SubmissionsResponse>("/admin/marketplace/submissions");
      setSubmissions(data.submissions || []);
      setSelected((data.submissions || [])[0] || null);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Failed to load submissions. Admin access may be required.");
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadSubmissions();
  }, []);

  async function act(action: "approve" | "reject" | "request-changes") {
    if (!selected) return;
    setMessage(null);
    setError(null);
    try {
      await apiPost(`/admin/marketplace/submissions/${submissionId(selected)}/${action}`, { notes });
      setMessage(`Submission ${action.replace("-", " ")} saved.`);
      setNotes("");
      await loadSubmissions();
    } catch (err) {
      setError(err instanceof Error ? err.message : "Review action failed.");
    }
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="admin" showMarketplace showAdmin showPlanBadge />

      <section className="mx-auto grid max-w-[1680px] gap-5 px-6 py-8 lg:grid-cols-[360px_1fr]">
        <aside className="rounded-2xl border border-slate-800 bg-slate-950/55 p-4">
          <h1 className="text-xl font-bold text-cyan-300">Review queue</h1>
          {loading ? <div className="mt-4 text-sm text-slate-400">Loading...</div> : null}
          <div className="mt-4 space-y-2">
            {submissions.map((item) => (
              <button key={submissionId(item)} onClick={() => setSelected(item)} className={`w-full rounded-xl border p-3 text-left text-sm transition ${submissionId(selected || {}) === submissionId(item) ? "border-cyan-700 bg-cyan-950/30" : "border-slate-800 bg-black/25 hover:bg-slate-900"}`}>
                <div className="font-semibold text-slate-100">{submissionName(item)}</div>
                <div className="mt-1 text-xs text-slate-400">{submissionKind(item)} · {item.status || "pending"} · {item.submitted_by || "unknown"}</div>
              </button>
            ))}
          </div>
          {!loading && submissions.length === 0 ? <div className="mt-4 text-sm text-slate-500">No submissions.</div> : null}
        </aside>

        <section className="rounded-2xl border border-slate-800 bg-slate-950/55 p-5">
          {error ? <div className="mb-4 rounded-xl border border-red-900/70 bg-red-950/30 p-4 text-red-200">{error}</div> : null}
          {message ? <div className="mb-4 rounded-xl border border-emerald-900/70 bg-emerald-950/30 p-4 text-emerald-200">{message}</div> : null}

          {selected ? (
            <div className="space-y-5">
              <div className="flex flex-wrap items-start justify-between gap-4">
                <div>
                  <div className="text-xs font-semibold uppercase text-cyan-300">Submission</div>
                  <h2 className="mt-1 text-2xl font-extrabold">{submissionName(selected)}</h2>
                  <div className="mt-1 text-sm text-slate-400">{submissionKind(selected)} · Status: {selected.status || "pending"}</div>
                </div>
              </div>

              <div className="grid gap-4 md:grid-cols-2">
                <div className="rounded-xl border border-slate-800 bg-black/30 p-4">
                  <h3 className="font-bold text-cyan-300">{submissionKind(selected)} JSON</h3>
                  <pre className="mt-3 max-h-[420px] overflow-auto whitespace-pre-wrap text-xs text-slate-200">{JSON.stringify(selected.workflow_json || selected.agent_json || {}, null, 2)}</pre>
                </div>
                <div className="rounded-xl border border-slate-800 bg-black/30 p-4">
                  <h3 className="font-bold text-cyan-300">Review notes</h3>
                  <textarea value={notes} onChange={(event) => setNotes(event.target.value)} className="mt-3 h-40 w-full resize-none rounded-xl border border-slate-700 bg-black/30 p-3 text-slate-100" placeholder="Approval notes, rejection reason, or requested changes" />
                  <div className="mt-4 flex flex-wrap gap-2">
                    <button onClick={() => act("approve")} className="rounded-xl bg-emerald-700 px-4 py-2 text-sm font-bold hover:bg-emerald-600">Approve</button>
                    <button onClick={() => act("request-changes")} className="rounded-xl border border-amber-700 px-4 py-2 text-sm font-semibold text-amber-100 hover:bg-amber-950/30">Request changes</button>
                    <button onClick={() => act("reject")} className="rounded-xl border border-red-800 px-4 py-2 text-sm font-semibold text-red-100 hover:bg-red-950/30">Reject</button>
                  </div>
                  <p className="mt-4 text-xs leading-5 text-slate-400">Approval creates a separate marketplace listing and version. The source private app or agent remains owned by the creator.</p>
                </div>
              </div>
            </div>
          ) : (
            <div className="text-slate-400">Select a submission to review.</div>
          )}
        </section>
      </section>
    </main>
  );
}
