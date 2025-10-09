"use client";

import { useEffect, useState } from "react";
import { createClient } from "@supabase/supabase-js";

// 🧩 Initialize Supabase client
const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

export default function WorkflowConsole({ jobId }: { jobId: string }) {
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");

  useEffect(() => {
    if (!jobId) return;

    const channelName = "realtime:public:workflows";
    console.log(`⚙️ Subscribing to Supabase channel: ${channelName}`);

    // 1️⃣ Initial fetch
    const fetchInitial = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single();

      if (error) console.error("❌ Initial fetch error:", error);
      if (data?.logs) setLogs(data.logs.split("\n"));
      if (data?.status) setStatus(data.status);
    };
    fetchInitial();

    // 2️⃣ Live realtime subscription
    const channel = supabase
      .channel(channelName)
      .on(
        "postgres_changes",
        {
          event: "*",
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
      .subscribe((status) => {
        console.log(`🧩 Realtime subscription: ${status}`);
      });

    // 3️⃣ Polling fallback (every 3 seconds)
    const poll = setInterval(async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single();

      if (error) {
        console.error("Polling error:", error);
        return;
      }

      if (data?.logs) setLogs(data.logs.split("\n"));
      if (data?.status) setStatus(data.status);
    }, 3000);

    // 4️⃣ Cleanup
    return () => {
      clearInterval(poll);
      supabase.removeChannel(channel);
    };
  }, [jobId]);

  // 🧠 Log coloring helper
  const colorFor = (line: string) => {
    if (line.includes("❌")) return "text-red-400";
    if (line.includes("✅")) return "text-green-400";
    if (line.includes("⚙️")) return "text-yellow-400";
    if (line.includes("🚀")) return "text-blue-400";
    if (line.includes("📘")) return "text-cyan-400";
    if (line.includes("🧠")) return "text-purple-400";
    return "text-gray-300";
  };

  return (
    <div className="mt-4 bg-gray-900 rounded-lg shadow-md p-4 font-mono text-sm text-green-400 h-72 overflow-y-auto border border-slate-700">
      <div className="text-yellow-400 border-b border-slate-700 mb-2 pb-1">
        🔴 Live Execution Feed — Status: {status.toUpperCase()}
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
