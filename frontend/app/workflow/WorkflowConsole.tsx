"use client";

import { useEffect, useState } from "react";
import { createClient } from "@supabase/supabase-js";

// 🧩 Supabase client
const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

// 🧱 Define the shape of a workflow row
interface WorkflowRow {
  id?: string;
  status?: string;
  logs?: string;
}

export default function WorkflowConsole({ jobId }: { jobId: string }) {
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");

  useEffect(() => {
    if (!jobId) return;

    const channelName = "realtime:public:workflows";
    console.log(`⚙️ Subscribing to Supabase channel: ${channelName}`);

    // 1️⃣ Fetch initial logs + status
    const fetchInitial = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status, logs")
        .eq("id", jobId)
        .single<WorkflowRow>();

      if (error) console.error("❌ Initial fetch error:", error);
      if (data?.logs
