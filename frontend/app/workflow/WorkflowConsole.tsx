"use client";

import { useEffect, useState } from "react";
import { createClient } from "@supabase/supabase-js";

const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

export default function WorkflowConsole({ jobId }: { jobId: string }) {
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");

  useEffect(() => {
    if (!jobId) return;

    // 🧩 Fetch initial logs
    const fetchInitial = async () => {
      const { data } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single();
      if (data?.logs) setLogs(data.logs.split("\n"));
      if (data?.status) setStatus(data.status);
    };
    fetchInitial();

    // ⚡ Subscribe to Realtime workflow updates
    const channel = supabase
      .channel("realtime:public:workflows")
      .on(
        "postgres_changes",
        {
          event: "UPDATE",
          schema: "public",
          table: "workflows",
          filter: `id=eq.${jobId}`,
        },
        (payload) => {
          console.log("📡 Realtime payload received:", payload);
          const updated = payload.new;
          if (updated?.logs) setLogs(updated.logs.split("\n"));
          if (updated?.status) setStatus(updated.status);
        }
      )
      .subscribe();

    return () => {
      supabase.removeChannel(channel);
    };
  }, [jobId]);

  const colorFor = (line: string) => {
    if (line.includes("❌")) return "text-red-400";
    if (line.includes("✅")) return "text-green-400";
    if (line.includes("⚙️")) return "text-yellow-400";
    if (line.includes("🏁")) return "text-cyan-400";
    return "text-gray-300";
  };

  return (
    <div className="mt-4 bg-gray-900 rounded-lg shadow-md p-4 font-mono text-sm text-green-400 h-72 overflow-y-auto border border-slate-700">
      <div className="text-yellow-400 border-b border-slate-700 mb-2 pb-1">
        Workflow Status: {status.toUpperCase()}
      </div>
      {logs.length === 0 ? (
        <div className="text-slate-400 italic">Waiting for updates...</div>
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
