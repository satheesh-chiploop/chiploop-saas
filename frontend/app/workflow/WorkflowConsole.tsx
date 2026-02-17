"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
//import { createClient } from "@supabase/supabase-js";

// 🧩 Supabase client
//const supabase = createClient(
//  process.env.NEXT_PUBLIC_SUPABASE_URL!,
//  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
// );

import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
const supabase = createClientComponentClient();

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
  const supabase = createClientComponentClient();
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "outputs">("live");
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState("starting");
  const [workflowMeta, setWorkflowMeta] = useState<WorkflowRow | null>(null);
  const consoleRef = useRef<HTMLDivElement | null>(null);
  const channelName = useMemo(() => `realtime:public:${table}`, [table]);
  const [refreshKey, setRefreshKey] = useState(0);
  const [focusedAgent, setFocusedAgent] = useState<string | null>(null);

  const [validationManifest, setValidationManifest] = useState<any | null>(null);
  const [validationManifestError, setValidationManifestError] = useState<string | null>(null);

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
  

  // ---------- 🧩 Render ----------
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
