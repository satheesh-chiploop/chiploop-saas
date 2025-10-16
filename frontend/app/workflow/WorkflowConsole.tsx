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
}

type TableName = "workflows" | "runs";

export default function WorkflowConsole({
  jobId,
  table = "workflows,runs",
}: {
  jobId: string;
  table?: TableName | string;
}) {
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");
  const consoleRef = useRef<HTMLDivElement | null>(null);

  const channelName = useMemo(() => `realtime:public:${table}`, [table]);

  useEffect(() => {
    if (!jobId) return;

    // 1️⃣ Initial fetch
    const fetchInitial = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single<WorkflowRow>();
      if (error) console.error("❌ Initial fetch error:", error);
      if (data?.logs) setLogs((data.logs || "").split("\n"));
      if (data?.status) setStatus(data.status || "unknown");
    };
    fetchInitial();

    // 2️⃣ Realtime subscription + polling fallback
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
            }
          )
          .subscribe((status) => {
            if (status === "SUBSCRIBED") {
              console.log(`✅ Subscribed to realtime for ${t}`);
            }
          });
        channels.push(ch);
      });
    } catch (err) {
      console.warn("⚠️ Realtime unavailable, will use polling fallback:", err);
    }

    // 3️⃣ Poll fallback (runs every 3s)
    const poller = setInterval(async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single<WorkflowRow>();
      if (!error && data) {
        if (data.logs) setLogs((data.logs || "").split("\n"));
        if (data.status) setStatus(data.status || "unknown");
      }
    }, 3000);

    // 4️⃣ Cleanup
    return () => {
      clearInterval(poller);
      channels.forEach((ch) => supabase.removeChannel(ch));
    };
  }, [jobId, table, channelName]);

  // ✅ Auto-scroll to bottom on new logs
  useEffect(() => {
    if (consoleRef.current) {
      consoleRef.current.scrollTop = consoleRef.current.scrollHeight;
    }
  }, [logs]);

  // 🎨 Log colors
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
    <div
      ref={consoleRef}
      className="mt-4 rounded-lg border border-slate-700 bg-slate-900/80 p-4 font-mono text-sm text-slate-200 shadow-md h-72 overflow-y-auto"
    >
      <div className="mb-2 border-b border-slate-700 pb-1 text-cyan-400">
        🔴 Live Execution Feed — Status:{" "}
        <span className="font-semibold">{status.toUpperCase()}</span>
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
