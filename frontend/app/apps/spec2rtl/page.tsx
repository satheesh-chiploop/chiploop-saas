"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import TextFileUpload from "@/components/TextFileUpload";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import { createClientComponentClient } from "@/lib/platformClient";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter((line) => line.trim().length > 0);
}

function mergeUploadedText(current: string, uploaded: string, mode: "append" | "replace") {
  if (mode === "append") return [current.trim(), uploaded.trim()].filter(Boolean).join("\n\n");
  return uploaded;
}

export default function Spec2RTLCheckPage() {
  const router = useRouter();
  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  const [projectName, setProjectName] = useState("");
  const [topModule, setTopModule] = useState("");
  const [specText, setSpecText] = useState("");
  const [rtlSourceMode, setRtlSourceMode] = useState<"from_arch2rtl" | "paste" | "repo_path">("from_arch2rtl");
  const [fromWorkflowId, setFromWorkflowId] = useState("");
  const [repoPath, setRepoPath] = useState("");
  const [pastedRtlFilesJson, setPastedRtlFilesJson] = useState("");

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    (async () => {
      setLoading(true);
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (!session?.user) {
        router.push("/login");
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const params = new URLSearchParams(window.location.search);
    const sourceId = params.get("from_workflow_id") || params.get("source_arch2rtl_workflow_id") || "";
    if (sourceId) {
      setRtlSourceMode("from_arch2rtl");
      setFromWorkflowId(sourceId);
    }
  }, [loading]);

  useEffect(() => {
    if (!workflowId) return;
    let active = true;
    const poll = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .maybeSingle();
      if (active && !error && data) setWorkflowRow(data as WorkflowRow);
    };
    void poll();
    const interval = window.setInterval(() => void poll(), 2000);
    return () => {
      active = false;
      window.clearInterval(interval);
    };
  }, [workflowId]);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  function authHeaders(): HeadersInit {
    const headers: Record<string, string> = {};
    if (sessionUserId) headers["x-user-id"] = sessionUserId;
    if (accessToken) headers.Authorization = `Bearer ${accessToken}`;
    return headers;
  }

  function parseMaybeJsonArray(raw: string): any[] | undefined {
    const trimmed = raw.trim();
    if (!trimmed) return undefined;
    const value = JSON.parse(trimmed);
    if (!Array.isArray(value)) throw new Error("Pasted RTL files must be a JSON array.");
    return value;
  }

  const canRun = useMemo(() => {
    if (running) return false;
    if (!specText.trim()) return false;
    if (rtlSourceMode === "from_arch2rtl" && !fromWorkflowId.trim()) return false;
    if (rtlSourceMode === "repo_path" && !repoPath.trim()) return false;
    if (rtlSourceMode === "paste" && !pastedRtlFilesJson.trim()) return false;
    return true;
  }, [running, specText, rtlSourceMode, fromWorkflowId, repoPath, pastedRtlFilesJson]);

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const body = {
        project_name: projectName || undefined,
        top_module: topModule || undefined,
        spec_text: specText,
        rtl_source_mode: rtlSourceMode,
        from_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
        source_arch2rtl_workflow_id: rtlSourceMode === "from_arch2rtl" ? fromWorkflowId : undefined,
        repo_path: rtlSourceMode === "repo_path" ? repoPath : undefined,
        pasted_rtl_files: rtlSourceMode === "paste" ? parseMaybeJsonArray(pastedRtlFilesJson) : undefined,
        toggles: { run_spec2rtl_check: true },
      };
      const resp = await fetch(`${API_BASE}/apps/spec2rtl/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", ...authHeaders() },
        body: JSON.stringify(body),
      });
      const text = await resp.text();
      const data = text ? JSON.parse(text) : {};
      if (!resp.ok) throw new Error(data?.detail || text || `${resp.status} ${resp.statusText}`);
      setWorkflowId(data.workflow_id);
      setRunId(data.run_id);
    } catch (error) {
      setErr(error instanceof Error ? error.message : String(error));
    } finally {
      setRunning(false);
    }
  }

  function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
  }

  if (loading) {
    return (
      <main className="flex min-h-screen items-center justify-center bg-black text-white">
        <div className="text-slate-300">Loading...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-black px-6 py-10 text-white">
      <div className="mx-auto max-w-6xl">
        <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
          Back to Apps
        </button>
        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Spec2RTL Check</h1>
          <p className="mt-2 max-w-3xl text-slate-300">
            Check whether generated, purchased, or vendor RTL appears consistent with the claimed spec. This is a conformance analysis, not a formal proof.
          </p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input value={projectName} onChange={(e) => setProjectName(e.target.value)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Top module (optional)</label>
              <input value={topModule} onChange={(e) => setTopModule(e.target.value)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">RTL source mode</label>
              <select value={rtlSourceMode} onChange={(e) => setRtlSourceMode(e.target.value as any)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                <option value="from_arch2rtl">From Arch2RTL workflow_id</option>
                <option value="repo_path">Repo path</option>
                <option value="paste">Paste RTL files JSON</option>
              </select>

              {rtlSourceMode === "from_arch2rtl" ? (
                <>
                  <label className="block text-sm text-slate-300">Arch2RTL workflow_id *</label>
                  <input value={fromWorkflowId} onChange={(e) => setFromWorkflowId(e.target.value)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />
                </>
              ) : null}
              {rtlSourceMode === "repo_path" ? (
                <>
                  <label className="block text-sm text-slate-300">Repo path *</label>
                  <input value={repoPath} onChange={(e) => setRepoPath(e.target.value)} className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />
                </>
              ) : null}
              {rtlSourceMode === "paste" ? (
                <>
                  <label className="block text-sm text-slate-300">Pasted RTL files JSON *</label>
                  <textarea
                    value={pastedRtlFilesJson}
                    onChange={(e) => setPastedRtlFilesJson(e.target.value)}
                    rows={8}
                    className="w-full rounded-xl border border-slate-800 bg-black/30 p-4 font-mono text-sm text-slate-100"
                    placeholder={'[{"path":"rtl/top.sv","content":"module top(...); endmodule"}]'}
                  />
                </>
              ) : null}

              <button onClick={runNow} disabled={!canRun} className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${canRun ? "bg-cyan-600 hover:bg-cyan-500" : "cursor-not-allowed bg-slate-700"}`}>
                {running ? "Starting..." : "Run Spec2RTL Check"}
              </button>
              {err ? <div className="text-sm text-red-300">{err}</div> : null}
            </div>

            <div>
              <TextFileUpload
                label="Upload claimed spec"
                helper="Load the spec, requirements, markdown, JSON, or register/interface notes."
                onText={(text, _fileName, mode) => setSpecText((current) => mergeUploadedText(current, text, mode))}
              />
              <label className="mt-4 block text-sm text-slate-300">Claimed spec *</label>
              <textarea
                value={specText}
                onChange={(e) => setSpecText(e.target.value)}
                rows={18}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste the claimed RTL spec, interface requirements, register behavior, reset behavior, and expected functions..."
              />
            </div>
          </div>
        </div>

        {workflowId ? (
          <div className="mt-6 grid gap-4 lg:grid-cols-[360px_minmax(0,1fr)]">
            <div className="rounded-2xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
              <div className="font-semibold text-slate-100">Run Status</div>
              <div className="mt-2">workflow_id: <span className="break-all text-slate-100">{workflowId}</span></div>
              <div className="mt-1">run_id: <span className="break-all text-slate-100">{runId}</span></div>
              <div className="mt-1">status: <span className="text-slate-100">{workflowRow?.status || "queued"}</span></div>
              <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">Download ZIP</button>
              <div ref={logsRef} className="mt-4 max-h-72 overflow-auto rounded-lg border border-slate-800 bg-black/30 p-3 font-mono text-xs text-slate-400">
                {logLines.map((line, index) => <div key={`${line}-${index}`}>{line}</div>)}
              </div>
            </div>
            <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowRow?.status} stage="arch2rtl" logs={workflowRow?.logs} />
          </div>
        ) : null}

        {workflowId ? (
          <div className="mt-6">
            <AskThisRunPanel workflowId={workflowId} compact />
          </div>
        ) : null}
      </div>
    </main>
  );
}
