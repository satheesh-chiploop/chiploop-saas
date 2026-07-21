"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { FiMic } from "react-icons/fi";
import { apiPost } from "@/lib/apiClient";
//import { createClient } from "@supabase/supabase-js";

// 🧩 Supabase client
//const supabase = createClient(
//  process.env.NEXT_PUBLIC_SUPABASE_URL!,
//  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
// );

import { createClientComponentClient } from "@/lib/platformClient";
const supabase = createClientComponentClient();

interface WorkflowRow {
  id?: string;
  status?: string;
  logs?: string;
  artifacts?: Record<string, any>;   
  created_at?: string;
  loop_type?: string;
}

type AskThisRunResponse = {
  workflow_id: string;
  question: string;
  answer: string;
  sources?: Array<{ type: string; path: string }>;
  source_count?: number;
  context_summary?: ContextSummary;
};

type ContextSummary = {
  mode: "smart" | "full";
  full_tokens_estimate: number;
  smart_tokens_estimate: number;
  active_tokens_estimate: number;
  reduction_percent: number;
  considered_count: number;
  included_count: number;
  skipped_count: number;
};

async function parseResponse(response: Response): Promise<unknown> {
  const text = await response.text();
  if (!text) return null;
  try {
    return JSON.parse(text);
  } catch {
    return { detail: text };
  }
}

function errorMessage(data: unknown, fallback: string): string {
  const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
  const detail = responseObject && "detail" in responseObject ? responseObject.detail : data;
  if (typeof detail === "string") return detail;
  const detailObject = detail && typeof detail === "object" ? (detail as Record<string, unknown>) : null;
  if (detailObject && typeof detailObject.message === "string") return detailObject.message;
  return fallback;
}



type TableName = "workflows" | "runs";

export default function WorkflowConsole({
  jobId,
  table = "workflows,runs",
}: {
  jobId: string;
  table?: TableName | string;
}) {
  const supabase = createClientComponentClient();
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "outputs" | "ask">("live");
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");
  const [workflowMeta, setWorkflowMeta] = useState<WorkflowRow | null>(null);
  const consoleRef = useRef<HTMLDivElement | null>(null);
  const channelName = useMemo(() => `realtime:public:${table}`, [table]);
  const [refreshKey, setRefreshKey] = useState(0);
  const [focusedAgent, setFocusedAgent] = useState<string | null>(null);

  const [validationManifest, setValidationManifest] = useState<any | null>(null);
  const [validationManifestError, setValidationManifestError] = useState<string | null>(null);
  const [askQuestion, setAskQuestion] = useState("");
  const [askLoading, setAskLoading] = useState(false);
  const [askError, setAskError] = useState<string | null>(null);
  const [askHistory, setAskHistory] = useState<AskThisRunResponse[]>([]);
  const [askContextMode, setAskContextMode] = useState<"smart" | "full">("smart");
  const [askVoiceRecording, setAskVoiceRecording] = useState(false);
  const [askVoiceBusy, setAskVoiceBusy] = useState(false);
  const [askVoiceStatus, setAskVoiceStatus] = useState<string | null>(null);
  const askVoiceRecorderRef = useRef<MediaRecorder | null>(null);
  const askVoiceStreamRef = useRef<MediaStream | null>(null);

    // ✅ Schematic / Mapping viewer
  const [viewOpen, setViewOpen] = useState(false);
  const [viewTitle, setViewTitle] = useState<string>("");
  const [viewText, setViewText] = useState<string>("");
  const [viewJson, setViewJson] = useState<any | null>(null);
  const [viewError, setViewError] = useState<string | null>(null);

  const normalizeStoragePath = (p: string) => {
    const s = (p || "").trim();
    if (!s) return s;
    if (s.startsWith("/")) return s.slice(1);
    return s;
  };
  const router = useRouter();

  function stopAskVoiceTracks() {
    askVoiceStreamRef.current?.getTracks().forEach((track) => track.stop());
    askVoiceStreamRef.current = null;
  }

  const fetchArtifactAsTextOrJson = async (path: string) => {
    setViewError(null);
    setViewText("");
    setViewJson(null);

    try {
      const { data, error } = await supabase.storage
        .from("artifacts")
        .createSignedUrl(normalizeStoragePath(path), 60);

      if (error) throw error;

      const resp = await fetch(data.signedUrl);
      if (!resp.ok) throw new Error(`Fetch failed (${resp.status})`);

      const contentType = resp.headers.get("content-type") || "";
      const text = await resp.text();

      // best-effort json parse
      if (contentType.includes("application/json") || path.endsWith(".json")) {
        try {
          const json = JSON.parse(text);
          setViewJson(json);
        } catch {
          setViewText(text);
        }
      } else {
        setViewText(text);
      }
    } catch (e: any) {
      console.error("❌ View fetch failed:", e);
      setViewError(e?.message || "Failed to load artifact");
    }
  };

  const openArtifactViewer = async (title: string, path: string) => {
    setViewTitle(title);
    setViewOpen(true);
    await fetchArtifactAsTextOrJson(path);
  };

  const extractDutPoints = (obj: any): string[] => {
    // Supports both: schematic shape and execution mapping shape
    const points = new Set<string>();

    const schematic =
      obj?.schematic ||
      obj?.bench_schematic ||
      obj?.bench_schematic_loaded ||
      obj;

    const rails =
      schematic?.connections?.rails ||
      obj?.mappings?.rails ||
      [];
    const probes =
      schematic?.connections?.probes ||
      obj?.mappings?.probes ||
      [];

    [...(rails || []), ...(probes || [])].forEach((x: any) => {
      (x?.dut_points || []).forEach((p: any) => points.add(String(p)));
    });

    return Array.from(points);
  };

  const renderSchematicMvp = (obj: any) => {
    if (!obj) return null;

    // If viewing bench_schematic_loaded.json, actual schematic is nested
    const schematic = obj?.schematic || obj;

    const bench = schematic?.bench || {};
    const dut = schematic?.dut || { name: "DUT" };
    const rails = schematic?.connections?.rails || [];
    const probes = schematic?.connections?.probes || [];

    const dutPoints = extractDutPoints(schematic);

    return (
      <div className="space-y-4">
        {/* Bench header */}
        <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
          <div className="text-cyan-300 font-semibold">Bench</div>
          <div className="text-slate-200 text-sm">
            <span className="font-semibold">{bench?.name || "Unknown Bench"}</span>
            {bench?.location ? <span className="text-slate-400"> — {bench.location}</span> : null}
          </div>
        </div>

        {/* Visual: Instruments -> DUT */}
        <div className="grid grid-cols-1 md:grid-cols-3 gap-3">
          {/* Left: Instruments (derived) */}
          <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
            <div className="text-cyan-300 font-semibold mb-2">Instruments</div>
            <div className="space-y-2 text-sm">
              {(schematic?.instruments || []).map((i: any) => (
                <div key={i.instrument_id} className="rounded bg-slate-800/60 p-2">
                  <div className="text-slate-200 font-semibold">
                    {i.nickname || i.instrument_type || "Instrument"}
                  </div>
                  <div className="text-[12px] text-slate-400">
                    {i.model ? `${i.vendor || ""} ${i.model}` : (i.vendor || "")}
                  </div>
                  <div className="text-[11px] text-slate-500 break-all">
                    {i.resource_string || ""}
                  </div>
                </div>
              ))}
              {(!schematic?.instruments || schematic.instruments.length === 0) && (
                <div className="text-slate-400 text-sm">No instruments listed in schematic.</div>
              )}
            </div>
          </div>

          {/* Center: DUT */}
          <div className="rounded-lg border border-cyan-700/60 bg-slate-900/40 p-3">
            <div className="text-cyan-300 font-semibold mb-2">DUT</div>
            <div className="rounded-lg border border-slate-700 bg-black/40 p-3">
              <div className="text-slate-100 font-semibold">
                {dut?.name || "DUT"}
              </div>
              {dut?.notes ? (
                <div className="text-[12px] text-slate-400 mt-1">{dut.notes}</div>
              ) : null}

              <div className="mt-3 text-[12px] text-slate-300 font-semibold">DUT Points</div>
              <div className="mt-2 flex flex-wrap gap-2">
                {(dutPoints.length ? dutPoints : ["VIN", "VOUT", "GND"]).map((p) => (
                  <span key={p} className="text-xs px-2 py-1 rounded bg-slate-800 text-slate-200 border border-slate-700">
                    {p}
                  </span>
                ))}
              </div>
            </div>
          </div>

          {/* Right: Connections summary */}
          <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
            <div className="text-cyan-300 font-semibold mb-2">Connections</div>

            <div className="text-slate-200 font-semibold text-sm">Rails</div>
            <div className="mt-2 space-y-2 text-sm">
              {(rails || []).map((r: any, idx: number) => (
                <div key={idx} className="rounded bg-slate-800/60 p-2">
                  <div className="text-slate-200">
                    <span className="font-semibold">{r.rail_name || "Rail"}</span>
                    <span className="text-slate-400"> → DUT {JSON.stringify(r.dut_points || [])}</span>
                  </div>
                  {r.psu?.instrument_id ? (
                    <div className="text-[12px] text-slate-400">
                      PSU: {r.psu.instrument_id} CH{r.psu.channel ?? "?"}
                    </div>
                  ) : null}
                  {r.sense?.dmm_instrument_id ? (
                    <div className="text-[12px] text-slate-400">
                      Sense: {r.sense.dmm_instrument_id} ({r.sense.mode || "vdc"})
                    </div>
                  ) : null}
                </div>
              ))}
              {(!rails || rails.length === 0) && <div className="text-slate-400 text-sm">No rails defined.</div>}
            </div>

            <div className="mt-4 text-slate-200 font-semibold text-sm">Probes</div>
            <div className="mt-2 space-y-2 text-sm">
              {(probes || []).map((p: any, idx: number) => (
                <div key={idx} className="rounded bg-slate-800/60 p-2">
                  <div className="text-slate-200">
                    <span className="font-semibold">{p.signal_name || "Signal"}</span>
                    <span className="text-slate-400"> → DUT {JSON.stringify(p.dut_points || [])}</span>
                  </div>
                  {p.scope?.instrument_id ? (
                    <div className="text-[12px] text-slate-400">
                      Scope: {p.scope.instrument_id} CH{p.scope.channel ?? "?"}
                    </div>
                  ) : null}
                </div>
              ))}
              {(!probes || probes.length === 0) && <div className="text-slate-400 text-sm">No probes defined.</div>}
            </div>
          </div>
        </div>
      </div>
    );
  };

  const renderExecutionMappingMvp = (obj: any) => {
    if (!obj) return null;
    const rails = obj?.mappings?.rails || [];
    const probes = obj?.mappings?.probes || [];
    const dutPoints = extractDutPoints(obj);

    return (
      <div className="space-y-4">
        <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
          <div className="text-cyan-300 font-semibold">Execution Mapping</div>
          <div className="text-slate-300 text-sm">
            Bench: <span className="text-slate-200">{obj?.bench_id}</span>
            {"  "} Executor: <span className="text-slate-200">{obj?.executor || "stub"}</span>
          </div>
        </div>

        <div className="rounded-lg border border-cyan-700/60 bg-slate-900/40 p-3">
          <div className="text-cyan-300 font-semibold">DUT</div>
          <div className="mt-2 flex flex-wrap gap-2">
            {(dutPoints.length ? dutPoints : ["VIN", "VOUT", "GND"]).map((p) => (
              <span key={p} className="text-xs px-2 py-1 rounded bg-slate-800 text-slate-200 border border-slate-700">
                {p}
              </span>
            ))}
          </div>
        </div>

        <div className="grid grid-cols-1 md:grid-cols-2 gap-3">
          <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
            <div className="text-slate-200 font-semibold">Rails</div>
            <div className="mt-2 space-y-2 text-sm">
              {rails.map((r: any, idx: number) => (
                <div key={idx} className="rounded bg-slate-800/60 p-2">
                  <div className="text-slate-200 font-semibold">{r.rail_name}</div>
                  <div className="text-[12px] text-slate-400">
                    PSU: {r.psu?.nickname || r.psu?.instrument_id} CH{r.psu?.channel ?? "?"}
                  </div>
                  {r.sense?.instrument_id || r.sense?.nickname ? (
                    <div className="text-[12px] text-slate-400">
                      Sense: {r.sense?.nickname || r.sense?.instrument_id} ({r.sense?.mode || "vdc"})
                    </div>
                  ) : null}
                  <div className="text-[12px] text-slate-500">DUT: {JSON.stringify(r.dut_points || [])}</div>
                </div>
              ))}
              {rails.length === 0 && <div className="text-slate-400 text-sm">No rail mappings.</div>}
            </div>
          </div>

          <div className="rounded-lg border border-slate-700 bg-slate-900/40 p-3">
            <div className="text-slate-200 font-semibold">Probes</div>
            <div className="mt-2 space-y-2 text-sm">
              {probes.map((p: any, idx: number) => (
                <div key={idx} className="rounded bg-slate-800/60 p-2">
                  <div className="text-slate-200 font-semibold">{p.signal_name}</div>
                  <div className="text-[12px] text-slate-400">
                    Scope: {p.scope?.nickname || p.scope?.instrument_id} CH{p.scope?.channel ?? "?"}
                  </div>
                  <div className="text-[12px] text-slate-500">DUT: {JSON.stringify(p.dut_points || [])}</div>
                </div>
              ))}
              {probes.length === 0 && <div className="text-slate-400 text-sm">No probe mappings.</div>}
            </div>
          </div>
        </div>

        {Array.isArray(obj?.issues) && obj.issues.length > 0 && (
          <div className="rounded-lg border border-yellow-700/60 bg-slate-900/40 p-3">
            <div className="text-yellow-300 font-semibold mb-2">Issues</div>
            <pre className="text-xs text-slate-200 whitespace-pre-wrap">
              {JSON.stringify(obj.issues, null, 2)}
            </pre>
          </div>
        )}
      </div>
    );
  };


  const findArtifactPath = (artifacts: any, needle: string): string | null => {
    if (!artifacts) return null;
  
    // artifacts can be:
    // 1) { "some_key": "backend/..." }
    // 2) { "Agent Name": { "subKey": "backend/..." } }
    for (const [k, v] of Object.entries(artifacts)) {
      if (!v) continue;
  
      if (typeof v === "string") {
        if (v.includes(needle)) return v;
        continue;
      }
  
      if (typeof v === "object") {
        for (const subVal of Object.values(v as Record<string, any>)) {
          if (typeof subVal === "string" && subVal.includes(needle)) return subVal;
        }
      }
    }
  
    return null;
  };
  useEffect(() => {
    const loadManifest = async () => {
      setValidationManifest(null);
      setValidationManifestError(null);
  
      if (workflowMeta?.loop_type !== "validation") return;
  
      const artifacts = workflowMeta?.artifacts;
      const manifestPath = findArtifactPath(artifacts, "validation/run_manifest.json");
      if (!manifestPath) return;
  
      try {
        const { data, error } = await supabase.storage
          .from("artifacts")
          .createSignedUrl(manifestPath, 60);
  
        if (error) throw error;
  
        const resp = await fetch(data.signedUrl);
        if (!resp.ok) throw new Error(`Manifest fetch failed (${resp.status})`);
        const json = await resp.json();
  
        setValidationManifest(json);
      } catch (e: any) {
        console.error("❌ Failed to load validation manifest:", e);
        setValidationManifestError(e?.message || "Failed to load manifest");
      }
    };
  
    loadManifest();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [workflowMeta?.loop_type, workflowMeta?.artifacts]);
    
  
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
  useEffect(() => {
    return () => {
      const recorder = askVoiceRecorderRef.current;
      if (recorder && recorder.state !== "inactive") {
        recorder.onstop = null;
        recorder.stop();
      }
      stopAskVoiceTracks();
    };
  }, []);

  const [wfId, setWfId] = useState<string>(jobId);
  // ---------- 🧠 FETCH + LIVE SYNC ----------
  useEffect(() => {
    if (!jobId) return;

    let cancelled = false;

    const resolveWorkflowId = async (): Promise<string> => {
      // Try jobId as workflow id first
      const wfTry = await supabase
        .from("workflows")
        .select("id")
        .eq("id", jobId)
        .maybeSingle();

      if (wfTry.data?.id) return jobId;

      // If not found, treat jobId as run id and map -> workflow_id
      const runTry = await supabase
        .from("runs")
        .select("workflow_id")
        .eq("id", jobId)
        .maybeSingle();

      return runTry.data?.workflow_id || jobId; // fallback
    };

    const start = async () => {
      const resolved = await resolveWorkflowId();
      if (cancelled) return;
      setWfId(resolved);

      // Initial fetch from workflows using resolved workflow id
      const { data, error } = await supabase
        .from("workflows")
        .select("id, status, created_at, loop_type, logs, artifacts")
        .eq("id", resolved)
        .maybeSingle<WorkflowRow>();

      if (error) console.error("❌ Initial workflow fetch error:", error);
      if (data) {
        setWorkflowMeta(data);
        if (typeof data.logs === "string" && data.logs.trim()) setLogs(data.logs.split("\n"));
        if (data.status) setStatus(data.status);
      }
    };

    start();

    // Realtime subscription
    const tables = table.split(",");
    const channels: any[] = [];

    try {
      tables.forEach((t) => {
        const filter =
          t.trim() === "runs"
            ? `workflow_id=eq.${jobId}` // ✅ runs filtered by workflow_id
            : `id=eq.${jobId}`;         // ✅ workflows filtered by id

        const ch = supabase
          .channel(`realtime:public:${t}`)
          .on(
            "postgres_changes",
            { event: "*", schema: "public", table: t.trim(), filter },
            (payload) => {
              const updated = payload.new as any;

              // If workflow row changes
              if (t.trim() === "workflows") {
                if (typeof updated?.logs === "string") setLogs(updated.logs.split("\n"));
                if (updated?.status) setStatus(updated.status || "unknown");
                if (updated?.artifacts) setWorkflowMeta(updated);
              }

              // If run row changes
              if (t.trim() === "runs") {
                const runLogs = typeof updated?.logs === "string" ? updated.logs : "";
                if (runLogs) {
                  setLogs((prev) => {
                    const merged = [...prev, ...runLogs.split("\n")].filter(Boolean);
                    return merged;
                  });
                }
              }
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
      const resolved = wfId || jobId;

      const [workflowData, runData] = await Promise.all([
        supabase
          .from("workflows")
          .select("status, logs, artifacts, created_at, loop_type")
          .eq("id", resolved)
          .maybeSingle<WorkflowRow>(),
        supabase
          .from("runs")
          .select("logs")
          .eq("workflow_id", resolved)
          .order("created_at", { ascending: false })
          .limit(1)
          .maybeSingle<any>(),
      ]);

      const wf = workflowData.data || {};
      const runLogs = runData.data?.logs || "";
      const allLogs = ((wf.logs || "") + "\n" + runLogs).trim();

      if (allLogs) setLogs(allLogs.split("\n"));
      if (wf.status) setStatus(wf.status || "unknown");
      if (Object.keys(wf).length) setWorkflowMeta(wf);
    }, 1000);

    return () => {
      cancelled = true;
      clearInterval(poller);
      channels.forEach((ch) => supabase.removeChannel(ch));
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [jobId, table, refreshKey, wfId]);

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

  const handleDownloadAllArtifacts = async () => {
    try {
      const res = await fetch(
        `${process.env.NEXT_PUBLIC_API_URL || "/api"}/workflow/${jobId}/download_zip`,
        { method: "GET" }
      );
  
      if (!res.ok) {
        throw new Error("Failed to download zip");
      }
  
      const blob = await res.blob();
      const url = window.URL.createObjectURL(blob);
  
      const a = document.createElement("a");
      a.href = url;
      a.download = `workflow_${jobId}_artifacts.zip`;
      a.click();
  
      window.URL.revokeObjectURL(url);
    } catch (err) {
      console.error("❌ ZIP download failed:", err);
      alert("Failed to download workflow artifacts.");
    }
  };
  

  const askThisRun = async (questionOverride?: string) => {
    const question = (questionOverride || askQuestion).trim();
    if (!question || askLoading) return;
    setAskLoading(true);
    setAskError(null);
    try {
      const response = await apiPost<AskThisRunResponse>(`/workflow/${wfId || jobId}/ask`, { question, context_mode: askContextMode });
      setAskHistory((current) => [response, ...current].slice(0, 10));
      setAskQuestion("");
      setActiveTab("ask");
    } catch (err: any) {
      setAskError(err?.message || "Ask This Run failed.");
    } finally {
      setAskLoading(false);
    }
  };

  // ---------- 🧩 Render ----------
  const askAuthHeaders = async (): Promise<Record<string, string>> => {
    const {
      data: { session },
    } = await supabase.auth.getSession();
    return session?.access_token ? { Authorization: `Bearer ${session.access_token}` } : {};
  };

  const toggleAskVoiceRecording = async () => {
    setAskError(null);
    setAskVoiceStatus(null);

    const activeRecorder = askVoiceRecorderRef.current;
    if (askVoiceRecording && activeRecorder && activeRecorder.state !== "inactive") {
      activeRecorder.stop();
      setAskVoiceRecording(false);
      return;
    }

    if (!navigator.mediaDevices?.getUserMedia || typeof MediaRecorder === "undefined") {
      setAskError("Voice recording is not supported in this browser.");
      return;
    }

    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      const recorder = new MediaRecorder(stream);
      const chunks: BlobPart[] = [];
      askVoiceStreamRef.current = stream;

      recorder.ondataavailable = (event) => {
        if (event.data.size > 0) chunks.push(event.data);
      };

      recorder.onstop = async () => {
        stopAskVoiceTracks();
        askVoiceRecorderRef.current = null;
        setAskVoiceBusy(true);
        try {
          const form = new FormData();
          form.append("file", new Blob(chunks, { type: "audio/webm" }), `ask-this-run-${Date.now()}.webm`);
          const response = await fetch("/api/studio/voice/transcribe", {
            method: "POST",
            headers: await askAuthHeaders(),
            body: form,
            cache: "no-store",
          });
          const data = await parseResponse(response);
          if (!response.ok) throw new Error(errorMessage(data, `Transcription failed with status ${response.status}.`));
          const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
          const transcript = String(responseObject?.transcript || "").trim();
          if (!transcript) throw new Error("No transcript returned.");
          setAskQuestion((current) => [current.trim(), transcript].filter(Boolean).join("\n\n"));
          setAskVoiceStatus("Transcript added.");
          setActiveTab("ask");
        } catch (err) {
          setAskError(err instanceof Error ? err.message : "Voice transcription failed.");
        } finally {
          setAskVoiceBusy(false);
        }
      };

      recorder.start();
      askVoiceRecorderRef.current = recorder;
      setAskVoiceRecording(true);
    } catch (err) {
      stopAskVoiceTracks();
      setAskVoiceRecording(false);
      setAskError(err instanceof Error ? err.message : "Microphone permission was not granted.");
    }
  };

  const renderSummary = () => (
    <div className="space-y-2">
      <div><strong>ID:</strong> {workflowMeta?.id}</div>
      <div><strong>Loop Type:</strong> {workflowMeta?.loop_type}</div>
      <div><strong>Status:</strong> {workflowMeta?.status?.toUpperCase()}</div>
      <div><strong>Created:</strong> {workflowMeta?.created_at}</div>
      {workflowMeta?.loop_type === "validation" && (
        <div className="mt-2 rounded border border-slate-700 bg-slate-900/40 p-2">
          <div className="text-cyan-300 font-semibold mb-1">🧪 Validation Context</div>
          {validationManifestError && (
            <div className="text-red-300 text-xs">
              Failed to load run manifest: {validationManifestError}
            </div>
          )}

          {!validationManifest && !validationManifestError && (
            <div className="text-slate-400 text-xs italic">
              Waiting for validation manifest...
            </div>
          )}

          {validationManifest && (
            <div className="space-y-1 text-xs text-slate-200">
              {/* Try common shapes, but remain robust */}
              {Array.isArray(validationManifest?.instruments) && (
                <div>
                  <span className="text-slate-400">Instruments:</span>{" "}
                  {validationManifest.instruments
                    .map((x: any) => x?.nickname || x?.id || String(x))
                    .join(", ")}
                </div>
              )}

              {Array.isArray(validationManifest?.instrument_ids) && (
                <div>
                  <span className="text-slate-400">Instrument IDs:</span>{" "}
                  {validationManifest.instrument_ids.join(", ")}
                </div>
              )}

              {validationManifest?.dut && (
                <div>
                  <span className="text-slate-400">DUT:</span>{" "}
                  {typeof validationManifest.dut === "string"
                    ? validationManifest.dut
                    : JSON.stringify(validationManifest.dut)}
                </div>
              )}
            </div>
          )}
        </div>
      )}

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

  const renderAsk = () => {
    const suggestions = [
      "Summarize this run and the key artifacts.",
      "What should I inspect first?",
      "Are there warnings, failures, or missing outputs?",
      "What is the recommended next step?",
    ];

    return (
      <div className="space-y-4">
        <div className="rounded-lg border border-cyan-800/60 bg-cyan-950/20 p-4">
          <div className="font-semibold text-cyan-200">Ask This Run</div>
          <p className="mt-1 text-sm text-cyan-100/80">
            Ask questions about this workflow&apos;s logs, reports, and artifact index. Answers are generated with AI from this run&apos;s available context.
          </p>
          <div className="mt-3 flex flex-wrap items-center justify-between gap-3 rounded-lg border border-slate-800 bg-slate-950/60 p-3">
            <div>
              <div className="text-sm font-semibold text-slate-100">Context mode</div>
              <p className="mt-1 text-xs leading-5 text-slate-400">
                Smart Context uses the most relevant logs and artifacts first. Full Context sends the broader run package.
              </p>
            </div>
            <div className="flex rounded-lg border border-slate-700 bg-slate-900 p-1 text-xs font-semibold">
              {(["smart", "full"] as const).map((mode) => (
                <button
                  key={mode}
                  type="button"
                  onClick={() => setAskContextMode(mode)}
                  className={`rounded-md px-3 py-1.5 capitalize transition ${
                    askContextMode === mode ? "bg-cyan-500 text-slate-950" : "text-slate-300 hover:bg-slate-800"
                  }`}
                >
                  {mode}
                </button>
              ))}
            </div>
          </div>
          <div className="mt-3 flex flex-wrap gap-2">
            {suggestions.map((suggestion) => (
              <button
                key={suggestion}
                type="button"
                disabled={askLoading}
                onClick={() => askThisRun(suggestion)}
                className="rounded border border-cyan-700 px-3 py-1 text-xs text-cyan-100 hover:bg-cyan-900/40 disabled:cursor-not-allowed disabled:opacity-50"
              >
                {suggestion}
              </button>
            ))}
          </div>
        </div>

        <form
          onSubmit={(event) => {
            event.preventDefault();
            askThisRun();
          }}
          className="space-y-3"
        >
          <textarea
            value={askQuestion}
            onChange={(event) => setAskQuestion(event.target.value)}
            placeholder="Ask about failures, warnings, generated files, coverage, handoff readiness..."
            className="min-h-24 w-full rounded-lg border border-slate-700 bg-slate-950 p-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
          />
          <div className="flex flex-wrap items-center gap-2">
            <button
              type="submit"
              disabled={askLoading || askQuestion.trim().length < 3}
              className="rounded bg-cyan-700 px-4 py-2 text-sm font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
            >
              {askLoading ? "Inspecting..." : "Ask this run"}
            </button>
            <button
              type="button"
              disabled={askVoiceBusy}
              onClick={toggleAskVoiceRecording}
              title={askVoiceRecording ? "Stop voice recording" : "Use voice input"}
              className={`inline-flex h-10 w-10 items-center justify-center rounded-lg border transition disabled:cursor-not-allowed disabled:opacity-50 ${
                askVoiceRecording
                  ? "border-red-500 bg-red-950/40 text-red-100 hover:bg-red-900/50"
                  : "border-cyan-800 bg-cyan-950/30 text-cyan-100 hover:bg-cyan-900/40"
              }`}
            >
              <FiMic aria-hidden="true" />
              <span className="sr-only">{askVoiceRecording ? "Stop voice recording" : "Use voice input"}</span>
            </button>
            {askVoiceBusy ? <span className="text-xs text-cyan-200">Transcribing...</span> : null}
            {askVoiceStatus ? <span className="text-xs text-cyan-200">{askVoiceStatus}</span> : null}
          </div>
        </form>

        {askError ? (
          <div className="rounded border border-red-800 bg-red-950/40 p-3 text-sm text-red-200">{askError}</div>
        ) : null}

        {askHistory.length === 0 && !askLoading ? (
          <div className="rounded border border-slate-700 bg-slate-900/40 p-4 text-sm text-slate-400">
            No questions asked yet.
          </div>
        ) : null}

        <div className="space-y-3">
          {askHistory.map((item, index) => (
            <div key={`${item.question}-${index}`} className="rounded-lg border border-slate-700 bg-slate-900/50 p-4">
              <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Question</div>
              <div className="mt-1 text-slate-100">{item.question}</div>
              <div className="mt-4 text-xs font-semibold uppercase text-cyan-300">Answer</div>
              <div className="mt-2 whitespace-pre-wrap leading-6 text-slate-200">{item.answer}</div>
              {item.context_summary ? (
                <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-3">
                  <div className="flex flex-wrap items-center gap-2 text-xs font-semibold uppercase tracking-wide text-slate-400">
                    <span>Context Used</span>
                    <span className="rounded-full border border-cyan-800 bg-cyan-950/40 px-2 py-0.5 text-cyan-200">
                      {item.context_summary.mode === "smart" ? "Smart Context" : "Full Context"}
                    </span>
                  </div>
                  <div className="mt-3 grid grid-cols-1 gap-2 text-sm sm:grid-cols-3">
                    <div className="rounded border border-slate-800 bg-slate-900/60 p-2">
                      <div className="text-xs text-slate-500">Smart estimate</div>
                      <div className="font-bold text-cyan-200">{item.context_summary.smart_tokens_estimate.toLocaleString()} tokens</div>
                    </div>
                    <div className="rounded border border-slate-800 bg-slate-900/60 p-2">
                      <div className="text-xs text-slate-500">Full estimate</div>
                      <div className="font-bold text-slate-100">{item.context_summary.full_tokens_estimate.toLocaleString()} tokens</div>
                    </div>
                    <div className="rounded border border-slate-800 bg-slate-900/60 p-2">
                      <div className="text-xs text-slate-500">Estimated reduction</div>
                      <div className="font-bold text-emerald-300">{item.context_summary.reduction_percent}%</div>
                    </div>
                  </div>
                  <div className="mt-2 text-xs text-slate-400">
                    Included {item.context_summary.included_count} of {item.context_summary.considered_count} evidence items.
                  </div>
                </div>
              ) : null}
              {item.sources && item.sources.length > 0 ? (
                <div className="mt-4">
                  <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Sources</div>
                  <div className="mt-2 flex flex-wrap gap-2">
                    {item.sources.slice(0, 8).map((source) => (
                      <span key={`${source.type}-${source.path}`} className="rounded bg-slate-800 px-2 py-1 text-xs text-slate-300">
                        {source.path}
                      </span>
                    ))}
                  </div>
                </div>
              ) : null}
            </div>
          ))}
        </div>
      </div>
    );
  };

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

    const isValidation = workflowMeta?.loop_type === "validation";
    const isValidationItem = (it: FlatItem) =>
      it.path.includes("/validation/") || it.path.includes("validation/");

    const sortedFlat = [...flat].sort((a, b) => {
      if (!isValidation) return 0;
      const av = isValidationItem(a) ? 0 : 1;
      const bv = isValidationItem(b) ? 0 : 1;
      if (av !== bv) return av - bv;
      return a.label.localeCompare(b.label);
    });

  
    // Apply focus filter (if node clicked)
    const filtered = focusedAgent
      ? sortedFlat.filter((item) =>
          item.agent.toLowerCase().startsWith(focusedAgent.toLowerCase())
        )
      : sortedFlat;
  
    // Group by agent
    const grouped: Record<string, FlatItem[]> = {};
    filtered.forEach((item) => {
      if (!grouped[item.agent]) grouped[item.agent] = [];
      grouped[item.agent].push(item);
    });


    return (
      <>
        <div className="mb-3 flex items-center justify-between rounded-xl border border-slate-800 bg-black/40 px-4 py-3">
          <div className="text-sm text-slate-300">
            <span className="font-semibold text-cyan-300">Studio</span>
            <span className="text-slate-500"> • build workflows</span>
          </div>
          <div className="flex items-center gap-2">
            <button
              onClick={() => router.push("/apps")}
              className="rounded-lg bg-cyan-600 px-3 py-2 text-sm font-semibold text-black hover:bg-cyan-500 transition"
              title="Go to Apps (default experience)"
            >
              Apps
            </button>
            <button
              onClick={() => router.push("/workflow")}
              className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-200 hover:bg-slate-900 transition"
              title="You are in Studio"
            >
              Studio
            </button>
          </div>
        </div>
    
        <div className="p-3 space-y-4">
          <button
            onClick={handleDownloadLogs}
            className="rounded bg-cyan-700 hover:bg-cyan-600 px-3 py-1 text-sm text-white"
          >
            ⬇️ Download All Logs
          </button>
    
          <button
            onClick={handleDownloadAllArtifacts}
            className="rounded bg-emerald-700 hover:bg-emerald-600 px-3 py-1 text-sm text-white"
          >
            📦 Download All Outputs (ZIP)
          </button>
    
          {/* 🧪 Validation Outputs (run-level, shown first) */}
          {workflowMeta?.loop_type === "validation" && (
            <div className="border border-slate-700 rounded-lg p-3 bg-slate-900/40">
              <div className="text-cyan-300 font-semibold mb-2">🧪 Validation Outputs</div>
    
              <div className="flex flex-wrap gap-2">
                {[
                  "validation/results.json",
                  "validation/results.csv",
                  "validation/run_manifest.json",
                  "validation/bench_schematic_loaded.json",
                  "validation/execution_mapping.json",
                  "validation/execution_mapping_summary.md",
                ].map((needle) => {
                  // find artifact path by substring match
                  let foundPath: string | null = null;
    
                  const consider = (candidate: string) => {
                    // Only allow Supabase storage objects
                    if (!candidate.startsWith("backend/")) return;
    
                    // First valid wins; storage-only avoids /artifacts/... routes
                    if (!foundPath) foundPath = candidate;
                  };
    
                  Object.values(workflowMeta?.artifacts || {}).forEach((v: any) => {
                    if (typeof v === "string" && v.includes(needle)) {
                      consider(v);
                    } else if (typeof v === "object") {
                      Object.values(v).forEach((sv: any) => {
                        if (typeof sv === "string" && sv.includes(needle)) {
                          consider(sv);
                        }
                      });
                    }
                  });
    
                  if (!foundPath) return null;
    
                  const label = needle.split("/").pop()!;
    
                  return (
                    <div key={needle} className="flex gap-2">
                      <button
                        onClick={() => openArtifactViewer(label, foundPath!)}
                        className="bg-slate-700 hover:bg-slate-600 text-white text-xs px-2 py-1 rounded"
                        title="View"
                      >
                        👁 {label}
                      </button>
    
                      <button
                        onClick={() => handleDownloadArtifact(foundPath!, `validation_${label}`)}
                        className="bg-cyan-700 hover:bg-cyan-600 text-white text-xs px-2 py-1 rounded"
                        title="Download"
                      >
                        ⬇️
                      </button>
                    </div>
                  );
                })}
              </div>
            </div>
          )}
    
          {focusedAgent && (
            <div className="mb-3 text-cyan-300 text-xs">
              🎯 Showing outputs for <strong>{focusedAgent}</strong>
              &nbsp;(click another agent to switch)
            </div>
          )}
    
          {Object.entries(grouped).map(([agent, items]) => (
            <div key={agent} className="border border-slate-700 rounded-lg p-3 bg-slate-800/50">
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
      </>
    );
    


  
    
  
  };

  return (
    <div className="mt-4 rounded-lg border border-slate-700 bg-slate-800/80 p-3 text-sm text-slate-200 shadow-md">
      {/* Tabs */}
      <div className="flex space-x-2 border-b border-slate-700 pb-2 mb-2">
        {["summary", "live", "outputs", "ask"].map((tab) => (
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
            {tab === "ask" && "Ask"}
          </button>
        ))}
      </div>

      {/* Content */}
      {activeTab === "summary" && renderSummary()}
      {activeTab === "live" && renderLogs()}
      {activeTab === "outputs" && renderOutputs()}
      {activeTab === "ask" && renderAsk()}

            {/* ✅ Artifact Viewer Modal */}
            {viewOpen && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
          <div className="w-[1100px] max-w-[96vw] max-h-[92vh] overflow-auto rounded-xl border border-slate-700 bg-slate-900 p-4 shadow-2xl">
            <div className="flex items-center justify-between mb-3">
              <div className="text-cyan-300 font-semibold">👁 {viewTitle}</div>
              <button
                className="text-slate-300 hover:text-white"
                onClick={() => setViewOpen(false)}
              >
                ✕
              </button>
            </div>

            {viewError && (
              <div className="rounded border border-red-700 bg-red-950/40 p-3 text-red-200 text-sm">
                {viewError}
              </div>
            )}

            {!viewError && !viewJson && !viewText && (
              <div className="text-slate-400 text-sm">Loading...</div>
            )}

            {!viewError && viewJson && (
              <div className="space-y-4">
                {/* Render schematic / mapping visually when recognized */}
                {viewTitle.includes("bench_schematic") && renderSchematicMvp(viewJson)}
                {viewTitle.includes("execution_mapping") && renderExecutionMappingMvp(viewJson)}

                {/* Fallback: raw JSON */}
                <div className="rounded-lg border border-slate-700 bg-black/40 p-3">
                  <div className="text-slate-200 font-semibold mb-2">Raw JSON</div>
                  <pre className="text-xs text-slate-200 whitespace-pre-wrap">
                    {JSON.stringify(viewJson, null, 2)}
                  </pre>
                </div>
              </div>
            )}

            {!viewError && !viewJson && viewText && (
              <div className="rounded-lg border border-slate-700 bg-black/40 p-3">
                <pre className="text-xs text-slate-200 whitespace-pre-wrap">
                  {viewText}
                </pre>
              </div>
            )}
          </div>
        </div>
      )}


      {/* Footer */}
      <div className="mt-2 text-right text-cyan-400 border-t border-slate-700 pt-1">
        Status: <span className="font-semibold">{status.toUpperCase()}</span>
      </div>
    </div>
  );
}
