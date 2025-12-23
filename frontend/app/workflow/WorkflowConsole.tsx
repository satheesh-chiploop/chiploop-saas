"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { createClient } from "@supabase/supabase-js";

// 🧩 Supabase client
const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);


interface WorkflowRow {
  id?: string;
  status?: string;
  logs?: string;
  artifacts?: Record<string, any>;   
  created_at?: string;
  loop_type?: string;
}



type TableName = "workflows" | "runs";

export default function WorkflowConsole({
  jobId,
  table = "workflows,runs",
}: {
  jobId: string;
  table?: TableName | string;
}) {
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "outputs">("live");
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");
  const [workflowMeta, setWorkflowMeta] = useState<WorkflowRow | null>(null);
  const consoleRef = useRef<HTMLDivElement | null>(null);
  const channelName = useMemo(() => `realtime:public:${table}`, [table]);
  const [refreshKey, setRefreshKey] = useState(0);
  const [focusedAgent, setFocusedAgent] = useState<string | null>(null);
  
  
  useEffect(() => {
    const handler = (e: any) => setFocusedAgent(e.detail);
    window.addEventListener("selectAgent", handler);
    return () => window.removeEventListener("selectAgent", handler);
  }, []);


  // 🔁 Reload WorkflowConsole when global refresh happens
  useEffect(() => {
    const refreshHandler = () => {
      console.log("🔄 Refreshing WorkflowConsole...");
      setRefreshKey((prev) => prev + 1);
  };
    window.addEventListener("refreshWorkflows", refreshHandler);
    return () => window.removeEventListener("refreshWorkflows", refreshHandler);
  }, []);

  // ---------- 🧠 FETCH + LIVE SYNC ----------
  useEffect(() => {
    if (!jobId) return;

    // Initial summary fetch
    const fetchSummary = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id, status, created_at, loop_type, logs, artifacts")
        .eq("id", jobId)
        .single<WorkflowRow>();
      if (error) console.error("❌ Initial fetch error:", error);
      if (data) {
        setWorkflowMeta(data);
        if (data.logs) setLogs(data.logs.split("\n"));
        if (data.status) setStatus(data.status);
      }
    };
    fetchSummary();

    // Realtime subscription (if replication active)
    const tables = table.split(",");
    const channels: any[] = [];

    try {
      tables.forEach((t) => {
        const ch = supabase
          .channel(`realtime:public:${t}`)
          .on(
            "postgres_changes",
            { event: "*", schema: "public", table: t, filter: `id=eq.${jobId}` },
            (payload) => {
              const updated = payload.new as WorkflowRow;
              if (updated?.logs) setLogs((updated.logs || "").split("\n"));
              if (updated?.status) setStatus(updated.status || "unknown");
              if (updated?.artifacts) setWorkflowMeta(updated);
            }
          )
          .subscribe();
        channels.push(ch);
      });
    } catch (err) {
      console.warn("⚠️ Realtime unavailable, using polling fallback:", err);
    }

    // Poll fallback (every 1s)
    const poller = setInterval(async () => {
      const [workflowData, runData] = await Promise.all([
        supabase
          .from("workflows")
          .select("status, logs, artifacts, created_at, loop_type")
          .eq("id", jobId)
          .single<WorkflowRow>(),
        supabase
          .from("runs")
          .select("logs")
          .eq("workflow_id", jobId)
          .order("created_at", { ascending: true })
          .maybeSingle<WorkflowRow>(),
      ]);

      const wf = workflowData.data || {};
      const runLogs = runData.data?.logs || "";
      const allLogs = ((wf.logs || "") + "\n" + runLogs).trim();

      if (allLogs) setLogs(allLogs.split("\n"));
      if (wf.status) setStatus(wf.status || "unknown");
      setWorkflowMeta(wf);
    }, 1000);

    return () => {
      clearInterval(poller);
      channels.forEach((ch) => supabase.removeChannel(ch));
    };
  }, [jobId, table, channelName,refreshKey]);

  // ---------- 🌀 Auto-scroll ----------
  useEffect(() => {
    if (consoleRef.current) {
      consoleRef.current.scrollTop = consoleRef.current.scrollHeight;
    }
  }, [logs]);

  // ---------- 🎨 Colors ----------
  const colorFor = (line: string) => {
    if (line.includes("❌")) return "text-red-400";
    if (line.includes("✅")) return "text-green-400";
    if (line.includes("⚙️")) return "text-yellow-400";
    if (line.includes("🚀")) return "text-blue-400";
    if (line.includes("📘")) return "text-cyan-400";
    if (line.includes("🧠")) return "text-purple-400";
    return "text-slate-300";
  };

  // ---------- 💾 Download Logs ----------
  const handleDownloadLogs = () => {
    const blob = new Blob([logs.join("\n")], { type: "text/plain" });
    const url = window.URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${jobId}_logs.txt`;
    a.click();
    window.URL.revokeObjectURL(url);
  };

  // ---------- 📦 Download Artifact ----------
  const handleDownloadArtifact = async (path: string, label: string) => {
    try {
      const { data, error } = await supabase.storage
        .from("artifacts")
        .createSignedUrl(path, 60); // valid for 60 seconds
      if (error) throw error;
      const a = document.createElement("a");
      a.href = data.signedUrl;
      a.download = label || path.split("/").pop()!;
      a.click();
    } catch (err) {
      console.error("❌ Artifact download failed:", err);
      alert("Artifact not found or permission denied.");
    }
  };

  // ---------- 🧩 Render ----------
  const renderSummary = () => (
    <div className="space-y-2">
      <div><strong>ID:</strong> {workflowMeta?.id}</div>
      <div><strong>Loop Type:</strong> {workflowMeta?.loop_type}</div>
      <div><strong>Status:</strong> {workflowMeta?.status?.toUpperCase()}</div>
      <div><strong>Created:</strong> {workflowMeta?.created_at}</div>
      <div>
        <strong>Artifacts:</strong>{" "}
        {workflowMeta?.artifacts
          ? JSON.stringify(workflowMeta.artifacts, null, 2)
          : "No artifacts yet."}
      </div>
    </div>
  );

  const renderLogs = () => (
    <div
      ref={consoleRef}
      className="mt-2 rounded-lg border border-slate-700 bg-slate-900/80 p-3 font-mono text-sm text-slate-200 h-64 overflow-y-auto"
    >
      {logs.length === 0 ? (
        <div className="italic text-slate-400">Waiting for updates...</div>
      ) : (
        logs.map((line, idx) => (
          <div key={idx} className={`${colorFor(line)} mb-0.5`}>
            {line}
          </div>
        ))
      )}
    </div>
  );

  const renderOutputs = () => {
    const artifacts = workflowMeta?.artifacts;
  
    if (!artifacts || Object.keys(artifacts).length === 0) {
      return (
        <div className="p-3 text-slate-400 italic">
          No artifacts yet. Run the workflow to generate outputs.
        </div>
      );
    }
  
    type FlatItem = { agent: string; label: string; path: string };
    const flat: FlatItem[] = [];
  
    Object.entries(artifacts).forEach(([key, value]) => {
      if (!value) return;
  
      // --- Case 1: legacy flat key → string path
      if (typeof value === "string") {
        const [agentPart] = key.split("_agent_");
        const agent = agentPart ? `${agentPart}_agent` : "other";
        const label = key
          .replace(`${agentPart}_agent_`, "")
          .replace(/_/g, " ")
          .trim();
  
        flat.push({ agent, label: label || "artifact", path: value });
        return;
      }
  
      // --- Case 2: new per-agent dict (our current backend behavior)
      if (typeof value === "object") {
        Object.entries(value as Record<string, any>).forEach(([subKey, subVal]) => {
          if (typeof subVal !== "string") return;

          const SKIP_KEYS = new Set(["artifact", "artifact_log", "log", "code"]);
          if (SKIP_KEYS.has(subKey)) return;
    
  
          // Heuristic: only show Supabase-storage artifacts, not local /artifacts/...
          if (!subVal.startsWith("backend/")) return;
  
          flat.push({
            agent: key, // here 'key' is the agent name: "Digital RTL Agent", "Embedded Sim Agent", ...
            label: subKey.replace(/_/g, " "),
            path: subVal,
          });
        });
      }
    });

  
    if (flat.length === 0) {
      return (
        <div className="p-3 text-slate-400 italic">
          No downloadable artifacts yet. Run the workflow to generate outputs.
        </div>
      );
    }
  
    // Apply focus filter (if node clicked)
    const filtered = focusedAgent
      ? flat.filter((item) =>
          item.agent.toLowerCase().startsWith(focusedAgent.toLowerCase())
        )
      : flat;
  
    // Group by agent
    const grouped: Record<string, FlatItem[]> = {};
    filtered.forEach((item) => {
      if (!grouped[item.agent]) grouped[item.agent] = [];
      grouped[item.agent].push(item);
    });
  
    return (
      <div className="p-3 space-y-4">
        <button
          onClick={handleDownloadLogs}
          className="rounded bg-cyan-700 hover:bg-cyan-600 px-3 py-1 text-sm text-white"
        >
          ⬇️ Download All Logs
        </button>
  
        {focusedAgent && (
          <div className="mb-3 text-cyan-300 text-xs">
            🎯 Showing outputs for <strong>{focusedAgent}</strong>
            &nbsp;(click another agent to switch)
          </div>
        )}
  
        {Object.entries(grouped).map(([agent, items]) => (
          <div
            key={agent}
            className="border border-slate-700 rounded-lg p-3 bg-slate-800/50"
          >
            <h3 className="text-cyan-400 font-semibold mb-2">
              {agent.replace("_agent", "").toUpperCase()}
            </h3>
  
            <div className="space-y-1">
              {items.map(({ label, path }) => (
                <div
                  key={`${agent}-${label}-${path}`}
                  className="flex items-center justify-between bg-slate-700/60 p-2 rounded"
                >
                  <span className="text-slate-300 capitalize">{label}</span>
                  <button
                    onClick={() => handleDownloadArtifact(path, `${agent}_${label}`)}
                    className="bg-cyan-700 hover:bg-cyan-600 text-white text-xs px-2 py-1 rounded"
                  >
                    ⬇️ Download
                  </button>
                </div>
              ))}
            </div>
          </div>
        ))}
      </div>
    );
  };
  

  return (
    <div className="mt-4 rounded-lg border border-slate-700 bg-slate-800/80 p-3 text-sm text-slate-200 shadow-md">
      {/* Tabs */}
      <div className="flex space-x-2 border-b border-slate-700 pb-2 mb-2">
        {["summary", "live", "outputs"].map((tab) => (
          <button
            key={tab}
            className={`px-3 py-1 rounded-t-lg ${
              activeTab === tab
                ? "bg-cyan-700 text-white"
                : "bg-slate-700 text-slate-300 hover:bg-slate-600"
            }`}
            onClick={() => setActiveTab(tab as any)}
          >
            {tab === "summary" && "📘 Summary"}
            {tab === "live" && "🔴 Live Feed"}
            {tab === "outputs" && "📦 Outputs"}
          </button>
        ))}
      </div>

      {/* Content */}
      {activeTab === "summary" && renderSummary()}
      {activeTab === "live" && renderLogs()}
      {activeTab === "outputs" && renderOutputs()}

      {/* Footer */}
      <div className="mt-2 text-right text-cyan-400 border-t border-slate-700 pt-1">
        Status: <span className="font-semibold">{status.toUpperCase()}</span>
      </div>
    </div>
  );
}
