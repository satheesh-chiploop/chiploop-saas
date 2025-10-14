"use client";

import { useEffect, useMemo, useState } from "react";
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
}

type TableName = "workflows" | "runs";

export default function WorkflowConsole({
  jobId,
  table = "workflows", // ✅ default keeps current behavior
}: {
  jobId: string;
  table?: TableName;
}) {
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");

  const channelName = useMemo(
    () => `realtime:public:${table}`,
    [table]
  );

  useEffect(() => {
    if (!jobId) return;

    // 1) Initial fetch
    const fetchInitial = async () => {
      const { data, error } = await supabase
        .from(table)
        .select("status, logs")
        .eq("id", jobId)
        .single<WorkflowRow>();
      if (error) console.error("❌ Initial fetch error:", error);
      if (data?.logs) setLogs((data.logs || "").split("\n"));
      if (data?.status) setStatus(data.status || "unknown");
    };
    fetchInitial();

    // 2) Realtime subscription
    const channel = supabase
      .channel(channelName)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table, filter: `id=eq.${jobId}` },
        (payload) => {
          const updated = payload.new as WorkflowRow;
          if (updated?.logs) setLogs((updated.logs || "").split("\n"));
          if (updated?.status) setStatus(updated.status || "unknown");
        }
      )
      .subscribe();

    // 3) Poll fallback
    const poll = setInterval(async () => {
      const { data, error } = await supabase
        .from(table)
        .select("status, logs")
        .eq("id", jobId)
        .single<WorkflowRow>();
      if (error) return; // quiet
      if (data?.logs) setLogs((data.logs || "").split("\n"));
      if (data?.status) setStatus(data.status || "unknown");
    }, 3000);

    // 4) Cleanup
    return () => {
      clearInterval(poll);
      supabase.removeChannel(channel);
    };
  }, [jobId, table, channelName]);

  // 🎨 Colors for log lines
  const colorFor = (line: string) => {
    if (line.includes("❌")) return "text-red-400";
    if (line.includes("✅")) return "text-green-400";
    if (line.includes("⚙️")) return "text-yellow-400";
    if (line.includes("🚀")) return "text-blue-400";
    if (line.includes("📘")) return "text-cyan-400";
    if (line.includes("🧠")) return "text-purple-400";
    return "text-slate-300";
  };

  return (
    <div className="mt-4 rounded-lg border border-slate-700 bg-slate-900/80 p-4 font-mono text-sm text-slate-200 shadow-md h-72 overflow-y-auto">
      <div className="mb-2 border-b border-slate-700 pb-1 text-cyan-400">
        🔴 Live Execution Feed — Status: <span className="font-semibold">{status.toUpperCase()}</span>
      </div>

      {logs.length === 0 ? (
        <div className="italic text-slate-400">Waiting for updates...</div>
      ) : (
        logs.map((line, idx) => (
          <div key={idx} className={colorFor(line)}>
            {line}
          </div>
        ))
      )}
    </div>
  );
}
