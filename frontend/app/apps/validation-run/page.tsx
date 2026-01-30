"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

const API_BASE =
  process.env.NEXT_PUBLIC_API_BASE ||
  process.env.NEXT_PUBLIC_BACKEND_URL ||
  "http://localhost:8000";

type Bench = {
  id: string;
  name?: string | null;
  location?: string | null;
  status?: string | null;
  created_at?: string | null;
};

type Instrument = {
  id: string;
  nickname: string;
  vendor?: string | null;
  model?: string | null;
  instrument_type: string;
  interface: string;
  resource_string: string;
  is_default?: boolean;
};

type TestPlan = {
  id: string;
  name: string;
  description?: string | null;
  created_at?: string | null;
};

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

const PHASES = [
  { key: "Generate Lab Handoff", wf: "Validation_Generate_Lab_Handoff" },
  { key: "Create Bench", wf: "Validation_Create_Bench" },
  { key: "Preflight Bench", wf: "Validation_Preflight_Bench" },
  { key: "Hardware Test Run", wf: "Validation_Hardware_Test_Run" },
  { key: "Pattern Detection", wf: "Validation_Pattern_Detection" },
  { key: "Coverage Proposal", wf: "Validation_Coverage_Proposal" },
  { key: "Evolution Proposal", wf: "Validation_Evolution_Proposal" },
  { key: "Apply Proposal", wf: "Validation_Apply_Proposal" },
];

function cls(...parts: Array<string | false | null | undefined>) {
  return parts.filter(Boolean).join(" ");
}

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs
    .split("\n")
    .map((l) => l.trimEnd())
    .filter((l) => l.trim().length > 0);
}

function inferPhaseProgress(lines: string[]): Record<string, "done" | "running" | "skipped" | "pending"> {
  // We use the exact strings the orchestrator writes:
  // "▶️ Phase: <name>"
  // "✅ Phase done: <name>"
  // "⏭️ Skipped: <name>"
  const state: Record<string, "done" | "running" | "skipped" | "pending"> = {};
  for (const p of PHASES) state[p.key] = "pending";

  for (const line of lines) {
    const started = line.match(/^▶️ Phase:\s*(.+)$/);
    const done = line.match(/^✅ Phase done:\s*(.+)$/);
    const skipped = line.match(/^⏭️ Skipped:\s*(.+)$/);

    if (started) {
      const name = started[1]?.trim();
      if (name && state[name]) state[name] = "running";
    }
    if (done) {
      const name = done[1]?.trim();
      if (name && state[name]) state[name] = "done";
    }
    if (skipped) {
      const name = skipped[1]?.trim();
      if (name && state[name]) state[name] = "skipped";
    }
  }

  // If we have a running phase, ensure earlier pending phases remain pending
  // and later phases remain pending (no extra logic needed).
  return state;
}

export default function ValidationRunAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [email, setEmail] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);

  const [benches, setBenches] = useState<Bench[]>([]);
  const [instruments, setInstruments] = useState<Instrument[]>([]);
  const [plans, setPlans] = useState<TestPlan[]>([]);

  // Choice architecture defaults
  const [benchMode, setBenchMode] = useState<"use_existing" | "create_new">("use_existing");
  const [selectedBenchId, setSelectedBenchId] = useState<string>("");

  const [benchName, setBenchName] = useState("");
  const [benchLocation, setBenchLocation] = useState("");

  const [selectedInstrumentIds, setSelectedInstrumentIds] = useState<string[]>([]);
  const [planMode, setPlanMode] = useState<"use_existing" | "type_name">("use_existing");
  const [selectedPlanId, setSelectedPlanId] = useState<string>("");
  const [testPlanName, setTestPlanName] = useState("");

  const [applyProposal, setApplyProposal] = useState(false);

  const [advancedOpen, setAdvancedOpen] = useState(false);
  const [registerOpen, setRegisterOpen] = useState(false);

  // Register instrument fields (inline)
  const [regNickname, setRegNickname] = useState("");
  const [regVendor, setRegVendor] = useState("");
  const [regModel, setRegModel] = useState("");
  const [regType, setRegType] = useState("DMM");
  const [regTransport, setRegTransport] = useState("visa");
  const [regInterface, setRegInterface] = useState("usb");
  const [regResource, setRegResource] = useState("");

  // Run state
  const [running, setRunning] = useState(false);
  const [runErr, setRunErr] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const phaseProgress = useMemo(() => inferPhaseProgress(logLines), [logLines]);

  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    if (logsRef.current) {
      logsRef.current.scrollTop = logsRef.current.scrollHeight;
    }
  }, [logLines.length]);

  function authHeaders(): HeadersInit {
    const h: Record<string, string> = {};
    if (sessionUserId) h["x-user-id"] = sessionUserId;
    if (accessToken) h["Authorization"] = `Bearer ${accessToken}`;
    return h;
  }

  async function fetchJSON<T>(path: string): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, { headers: authHeaders() });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` — ${txt}` : ""}`);
    }
    return resp.json();
  }

  async function postJSON<T>(path: string, body: any): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...authHeaders() },
      body: JSON.stringify(body),
    });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` — ${txt}` : ""}`);
    }
    return resp.json();
  }

  // Auth gate + preload data
  useEffect(() => {
    (async () => {
      setLoading(true);

      const { data: { session } } = await supabase.auth.getSession();
      if (!session) {
        router.push("/login");
        return;
      }

      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setEmail(session.user.email || null);

      try {
        const [benchesRes, instRes, plansRes] = await Promise.all([
          fetchJSON<{ ok: boolean; benches: Bench[] }>("/validation/benches"),
          fetchJSON<{ ok: boolean; instruments: Instrument[] }>("/validation/instruments"),
          fetchJSON<{ status: string; plans: TestPlan[] }>("/validation/test_plans"),
        ]);

        const loadedBenches = benchesRes.benches || [];
        const loadedInst = instRes.instruments || [];
        const loadedPlans = plansRes.plans || [];

        setBenches(loadedBenches);
        setInstruments(loadedInst);
        setPlans(loadedPlans);

        // Nudges / defaults:
        // 1) If bench exists, default to "use existing" and preselect most recent.
        // 2) If no bench, default to "create new" and preselect default instruments.
        if (loadedBenches.length > 0) {
          setBenchMode("use_existing");
          setSelectedBenchId(loadedBenches[0].id);
        } else {
          setBenchMode("create_new");
        }

        // Default instruments:
        const defaultInst = loadedInst.filter((i) => i.is_default).map((i) => i.id);
        if (defaultInst.length > 0) {
          setSelectedInstrumentIds(defaultInst);
        } else if (loadedInst.length > 0) {
          // “Good enough” nudge: preselect first instrument to reduce empty states
          setSelectedInstrumentIds([loadedInst[0].id]);
        }

        // Default test plan:
        if (loadedPlans.length > 0) {
          setPlanMode("use_existing");
          setSelectedPlanId(loadedPlans[0].id);
        } else {
          setPlanMode("type_name");
        }

      } catch (e: any) {
        setRunErr(e?.message || String(e));
      } finally {
        setLoading(false);
      }
    })();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [router]);

  // Subscribe to workflow updates (live progress)
  useEffect(() => {
    if (!workflowId) return;

    let isActive = true;

    (async () => {
      // Fetch initial row
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .single();

      if (isActive) {
        if (!error && data) setWorkflowRow(data as any);
      }
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        {
          event: "*",
          schema: "public",
          table: "workflows",
          filter: `id=eq.${workflowId}`,
        },
        (payload) => {
          const row = payload.new as any;
          setWorkflowRow({
            id: row.id,
            status: row.status,
            phase: row.phase,
            logs: row.logs,
            updated_at: row.updated_at,
          });
        }
      )
      .subscribe();

    return () => {
      isActive = false;
      supabase.removeChannel(channel);
    };
  }, [workflowId]);

  const selectedBench = useMemo(
    () => benches.find((b) => b.id === selectedBenchId) || null,
    [benches, selectedBenchId]
  );

  const selectedPlan = useMemo(
    () => plans.find((p) => p.id === selectedPlanId) || null,
    [plans, selectedPlanId]
  );

  const canRun = useMemo(() => {
    if (running) return false;

    // Bench logic
    if (benchMode === "use_existing") {
      if (!selectedBenchId) return false;
    } else {
      if (!benchName.trim()) return false;
      if (selectedInstrumentIds.length === 0) return false;
    }

    // Test plan logic (MVP: allow either plan_id OR typed name OR empty; first workflow might generate)
    if (planMode === "use_existing") {
      // ok even if empty, but nudge: prefer selecting
      return true;
    } else {
      // allow empty too, but nudge recommends naming
      return true;
    }
  }, [running, benchMode, selectedBenchId, benchName, selectedInstrumentIds.length, planMode]);

  async function onRun() {
    setRunErr(null);
    setRunning(true);

    try {
      const create_new_bench = benchMode === "create_new";
      const bench_id = create_new_bench ? undefined : selectedBenchId;

      // Choice architecture: if using existing bench, we don’t force instrument selection
      // Instrument setup agent will pull bench instruments automatically.
      const instrument_ids = create_new_bench ? selectedInstrumentIds : (advancedOpen ? selectedInstrumentIds : undefined);

      const body = {
        bench_id,
        create_new_bench,
        bench_name: create_new_bench ? benchName.trim() : undefined,
        bench_location: create_new_bench ? (benchLocation.trim() || undefined) : undefined,
        instrument_ids: instrument_ids && instrument_ids.length > 0 ? instrument_ids : undefined,
        test_plan_id: planMode === "use_existing" ? (selectedPlanId || undefined) : undefined,
        test_plan_name: planMode === "type_name" ? (testPlanName.trim() || undefined) : undefined,
        toggles: {
          apply: applyProposal,
        },
      };

      const res = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>("/apps/validation/run", body);

      setWorkflowId(res.workflow_id);
      setRunId(res.run_id);
    } catch (e: any) {
      setRunErr(e?.message || String(e));
    } finally {
      setRunning(false);
    }
  }

  async function refreshListsSoft() {
    // Small “nudge” action after registering instrument
    try {
      const instRes = await fetchJSON<{ ok: boolean; instruments: Instrument[] }>("/validation/instruments");
      setInstruments(instRes.instruments || []);
    } catch {}
  }

  async function onRegisterInstrument() {
    setRunErr(null);
    try {
      if (!regNickname.trim() || !regType.trim() || !regInterface.trim() || !regResource.trim()) {
        setRunErr("Please provide nickname, type, interface, and resource string.");
        return;
      }

      const payload = {
        nickname: regNickname.trim(),
        vendor: regVendor.trim() || null,
        model: regModel.trim() || null,
        instrument_type: regType.trim(),
        transport: regTransport.trim(),
        interface: regInterface.trim(),
        resource_string: regResource.trim(),
      };

      await postJSON("/validation/instruments/register", payload);

      setRegisterOpen(false);
      setRegNickname("");
      setRegVendor("");
      setRegModel("");
      setRegResource("");

      await refreshListsSoft();
    } catch (e: any) {
      setRunErr(e?.message || String(e));
    }
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      {/* Top nav */}
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button onClick={() => router.push("/apps")} className="flex items-center gap-2 text-xl font-extrabold">
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">Validation Run</span>
          </button>

          <div className="flex items-center gap-3">
            <button
              onClick={() => router.push("/apps")}
              className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 transition"
            >
              ← Apps
            </button>
            <button
              onClick={() => router.push("/workflow")}
              className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900 transition"
              title="Advanced builder"
            >
              Studio
            </button>
          </div>
        </div>
      </div>

      {/* Header / nudge */}
      <section className="mx-auto max-w-6xl px-6 pt-10 pb-6">
        <div className="rounded-2xl border border-slate-800 bg-slate-900/25 p-6">
          <div className="flex flex-wrap items-start justify-between gap-3">
            <div>
              <div className="text-xs text-slate-400">
                Welcome{email ? `, ${email}` : ""} • <span className="text-cyan-300">Recommended</span>: run with preflight
              </div>
              <h1 className="mt-2 text-3xl font-extrabold">One click → Preflight → Hardware Run → Learn → Report</h1>
              <p className="mt-2 max-w-3xl text-slate-300">
                You provide inputs once. ChipLoop runs the full validation loop and produces run results + proposals +
                an executive report.
              </p>
              <div className="mt-3 text-xs text-slate-500">
                Nudge: Preflight prevents avoidable rerun failures (missing schematic / instrument readiness).
              </div>
            </div>

            <div className="rounded-2xl border border-cyan-900/60 bg-cyan-500/10 px-4 py-3">
              <div className="text-xs text-cyan-200">Default path</div>
              <div className="mt-1 text-sm text-slate-100">
                {benchMode === "use_existing" && benches.length > 0 ? "Use existing bench" : "Create a new bench"}
              </div>
              <div className="mt-1 text-xs text-slate-300">Fastest way to get a clean first run.</div>
            </div>
          </div>
        </div>
      </section>

      {/* Body */}
      <section className="mx-auto max-w-6xl px-6 pb-16 grid gap-6 lg:grid-cols-5">
        {/* Left: inputs */}
        <div className="lg:col-span-3 space-y-6">
          {/* Bench selection */}
          <div className="rounded-2xl border border-slate-800 bg-slate-900/15 p-6">
            <div className="flex items-start justify-between gap-3">
              <div>
                <div className="text-lg font-bold">1) Choose your bench</div>
                <div className="text-sm text-slate-400">
                  Recommended: use an existing bench if you have one (less typing, fewer mistakes).
                </div>
              </div>
              <span className="rounded-full border border-cyan-900/60 bg-cyan-500/10 px-3 py-1 text-xs text-cyan-200">
                Choice architecture
              </span>
            </div>

            <div className="mt-4 flex flex-wrap gap-2">
              <button
                onClick={() => setBenchMode("use_existing")}
                className={cls(
                  "rounded-xl px-4 py-2 text-sm border transition",
                  benchMode === "use_existing"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                )}
              >
                Use existing (recommended)
              </button>
              <button
                onClick={() => setBenchMode("create_new")}
                className={cls(
                  "rounded-xl px-4 py-2 text-sm border transition",
                  benchMode === "create_new"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                )}
              >
                Create new
              </button>
            </div>

            {benchMode === "use_existing" ? (
              <div className="mt-4">
                <label className="text-sm text-slate-300">Select bench</label>
                <select
                  value={selectedBenchId}
                  onChange={(e) => setSelectedBenchId(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-3 text-slate-100"
                >
                  {benches.length === 0 ? (
                    <option value="">No benches found — create a new bench</option>
                  ) : null}
                  {benches.map((b) => (
                    <option key={b.id} value={b.id}>
                      {(b.name || "Unnamed bench")} — {b.location || "No location"} — {b.id.slice(0, 8)}
                    </option>
                  ))}
                </select>

                {selectedBench ? (
                  <div className="mt-3 rounded-xl border border-slate-800 bg-slate-950/40 p-4 text-sm">
                    <div className="text-slate-200 font-semibold">Selected</div>
                    <div className="mt-1 text-slate-300">
                      {(selectedBench.name || "Unnamed bench")} • {selectedBench.location || "No location"}
                    </div>
                    <div className="mt-1 text-xs text-slate-500">
                      Nudge: reruns on the same bench are fastest. Preflight will ensure schematic exists.
                    </div>
                  </div>
                ) : null}
              </div>
            ) : (
              <div className="mt-4 grid gap-4 md:grid-cols-2">
                <div>
                  <label className="text-sm text-slate-300">Bench name (required)</label>
                  <input
                    value={benchName}
                    onChange={(e) => setBenchName(e.target.value)}
                    placeholder="e.g., Lab Bench A"
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-3 text-slate-100"
                  />
                </div>
                <div>
                  <label className="text-sm text-slate-300">Location (optional)</label>
                  <input
                    value={benchLocation}
                    onChange={(e) => setBenchLocation(e.target.value)}
                    placeholder="e.g., Building 3 / Rack 2"
                    className="mt-2 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-3 text-slate-100"
                  />
                </div>

                <div className="md:col-span-2 rounded-xl border border-slate-800 bg-slate-950/30 p-4">
                  <div className="text-sm font-semibold text-slate-100">Instruments for this bench</div>
                  <div className="text-xs text-slate-500 mt-1">
                    Recommended: pick your default instruments. You can register a new one below.
                  </div>

                  <div className="mt-3 grid gap-2 md:grid-cols-2">
                    {instruments.map((inst) => {
                      const checked = selectedInstrumentIds.includes(inst.id);
                      return (
                        <label
                          key={inst.id}
                          className={cls(
                            "flex items-start gap-3 rounded-xl border p-3 cursor-pointer transition",
                            checked
                              ? "border-cyan-700 bg-cyan-500/10"
                              : "border-slate-800 bg-black/30 hover:bg-black/40"
                          )}
                        >
                          <input
                            type="checkbox"
                            checked={checked}
                            onChange={() => {
                              setSelectedInstrumentIds((prev) =>
                                checked ? prev.filter((x) => x !== inst.id) : [...prev, inst.id]
                              );
                            }}
                            className="mt-1"
                          />
                          <div>
                            <div className="text-sm font-semibold text-slate-100">
                              {inst.nickname}{" "}
                              {inst.is_default ? (
                                <span className="ml-2 rounded-full border border-cyan-900/60 bg-cyan-500/10 px-2 py-0.5 text-xs text-cyan-200">
                                  default
                                </span>
                              ) : null}
                            </div>
                            <div className="text-xs text-slate-400">
                              {inst.instrument_type} • {inst.interface} • {inst.resource_string}
                            </div>
                          </div>
                        </label>
                      );
                    })}
                  </div>

                  <div className="mt-3 flex flex-wrap items-center gap-2">
                    <button
                      onClick={() => setRegisterOpen((v) => !v)}
                      className="rounded-xl border border-slate-700 bg-slate-950/40 px-4 py-2 text-sm hover:bg-slate-950 transition"
                    >
                      {registerOpen ? "Hide register" : "Register new instrument"}
                    </button>
                    <div className="text-xs text-slate-500">
                      Nudge: registering once enables faster reruns forever.
                    </div>
                  </div>

                  {registerOpen ? (
                    <div className="mt-4 rounded-2xl border border-slate-800 bg-black/30 p-4">
                      <div className="text-sm font-semibold">Register instrument</div>
                      <div className="mt-3 grid gap-3 md:grid-cols-2">
                        <div>
                          <label className="text-xs text-slate-400">Nickname *</label>
                          <input
                            value={regNickname}
                            onChange={(e) => setRegNickname(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., DMM_Keithley"
                          />
                        </div>
                        <div>
                          <label className="text-xs text-slate-400">Type *</label>
                          <input
                            value={regType}
                            onChange={(e) => setRegType(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., DMM / PSU / SMU"
                          />
                        </div>
                        <div>
                          <label className="text-xs text-slate-400">Vendor</label>
                          <input
                            value={regVendor}
                            onChange={(e) => setRegVendor(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., Keysight"
                          />
                        </div>
                        <div>
                          <label className="text-xs text-slate-400">Model</label>
                          <input
                            value={regModel}
                            onChange={(e) => setRegModel(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., 34465A"
                          />
                        </div>
                        <div>
                          <label className="text-xs text-slate-400">Transport</label>
                          <input
                            value={regTransport}
                            onChange={(e) => setRegTransport(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., visa"
                          />
                        </div>
                        <div>
                          <label className="text-xs text-slate-400">Interface *</label>
                          <input
                            value={regInterface}
                            onChange={(e) => setRegInterface(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder="e.g., usb / tcpip"
                          />
                        </div>
                        <div className="md:col-span-2">
                          <label className="text-xs text-slate-400">Resource string *</label>
                          <input
                            value={regResource}
                            onChange={(e) => setRegResource(e.target.value)}
                            className="mt-1 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-2 text-slate-100"
                            placeholder='e.g., USB0::0x0957::0x1234::MY123456::INSTR'
                          />
                        </div>
                      </div>

                      <div className="mt-4 flex gap-2">
                        <button
                          onClick={onRegisterInstrument}
                          className="rounded-xl bg-cyan-600 px-4 py-2 font-semibold hover:bg-cyan-500 transition"
                        >
                          Register
                        </button>
                        <button
                          onClick={() => setRegisterOpen(false)}
                          className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900 transition"
                        >
                          Cancel
                        </button>
                      </div>
                    </div>
                  ) : null}
                </div>
              </div>
            )}
          </div>

          {/* Test plan selection */}
          <div className="rounded-2xl border border-slate-800 bg-slate-900/15 p-6">
            <div className="flex items-start justify-between gap-3">
              <div>
                <div className="text-lg font-bold">2) Choose your test plan</div>
                <div className="text-sm text-slate-400">
                  Recommended: reuse an existing plan for iteration-2+ (fast + consistent).
                </div>
              </div>
              <span className="rounded-full border border-slate-700 bg-slate-950/30 px-3 py-1 text-xs text-slate-200">
                Nudge: reuse → faster reruns
              </span>
            </div>

            <div className="mt-4 flex flex-wrap gap-2">
              <button
                onClick={() => setPlanMode("use_existing")}
                className={cls(
                  "rounded-xl px-4 py-2 text-sm border transition",
                  planMode === "use_existing"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                )}
              >
                Use existing (recommended)
              </button>
              <button
                onClick={() => setPlanMode("type_name")}
                className={cls(
                  "rounded-xl px-4 py-2 text-sm border transition",
                  planMode === "type_name"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                )}
              >
                Type plan name
              </button>
            </div>

            {planMode === "use_existing" ? (
              <div className="mt-4">
                <label className="text-sm text-slate-300">Select test plan</label>
                <select
                  value={selectedPlanId}
                  onChange={(e) => setSelectedPlanId(e.target.value)}
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-3 text-slate-100"
                >
                  {plans.length === 0 ? <option value="">No test plans found</option> : null}
                  {plans.map((p) => (
                    <option key={p.id} value={p.id}>
                      {p.name} — {p.id.slice(0, 8)}
                    </option>
                  ))}
                </select>

                {selectedPlan ? (
                  <div className="mt-3 text-xs text-slate-500">
                    Selected: <span className="text-slate-200">{selectedPlan.name}</span>
                  </div>
                ) : null}
              </div>
            ) : (
              <div className="mt-4">
                <label className="text-sm text-slate-300">Test plan name (optional)</label>
                <input
                  value={testPlanName}
                  onChange={(e) => setTestPlanName(e.target.value)}
                  placeholder="e.g., DDR_Bringup_v2"
                  className="mt-2 w-full rounded-xl border border-slate-800 bg-black/40 px-3 py-3 text-slate-100"
                />
                <div className="mt-2 text-xs text-slate-500">
                  Nudge: naming helps future reruns and tracking.
                </div>
              </div>
            )}
          </div>

          {/* Advanced toggles */}
          <div className="rounded-2xl border border-slate-800 bg-slate-900/10 p-6">
            <button
              onClick={() => setAdvancedOpen((v) => !v)}
              className="w-full flex items-center justify-between rounded-xl border border-slate-800 bg-black/30 px-4 py-3 hover:bg-black/40 transition"
            >
              <div className="text-left">
                <div className="font-semibold">Advanced</div>
                <div className="text-xs text-slate-500">Optional controls. Keep off for fastest success.</div>
              </div>
              <div className="text-slate-300">{advancedOpen ? "−" : "+"}</div>
            </button>

            {advancedOpen ? (
              <div className="mt-4 grid gap-4 md:grid-cols-2">
                <label className="flex items-start gap-3 rounded-xl border border-slate-800 bg-black/30 p-4">
                  <input
                    type="checkbox"
                    checked={applyProposal}
                    onChange={(e) => setApplyProposal(e.target.checked)}
                    className="mt-1"
                  />
                  <div>
                    <div className="font-semibold">Auto-apply proposal</div>
                    <div className="text-xs text-slate-500">
                      Default OFF (recommended). Turn ON only when you trust the loop.
                    </div>
                  </div>
                </label>

                <div className="rounded-xl border border-slate-800 bg-black/30 p-4">
                  <div className="font-semibold">Instrument override</div>
                  <div className="mt-1 text-xs text-slate-500">
                    If you selected an existing bench, ChipLoop uses bench-mapped instruments by default.
                    Use overrides only if needed.
                  </div>
                  <div className="mt-3 text-xs text-slate-400">
                    Current selected instruments:{" "}
                    <span className="text-slate-200">{selectedInstrumentIds.length}</span>
                  </div>
                </div>
              </div>
            ) : null}
          </div>

          {/* Run CTA */}
          <div className="rounded-2xl border border-slate-800 bg-slate-900/15 p-6">
            <div className="flex items-start justify-between gap-3">
              <div>
                <div className="text-lg font-bold">3) Run</div>
                <div className="text-sm text-slate-400">
                  One click. We stream progress and generate an executive report.
                </div>
              </div>
              <span className="rounded-full border border-cyan-900/60 bg-cyan-500/10 px-3 py-1 text-xs text-cyan-200">
                Default: safe + repeatable
              </span>
            </div>

            {/* Run summary (commitment nudge) */}
            <div className="mt-4 rounded-2xl border border-slate-800 bg-black/30 p-5">
              <div className="text-sm font-semibold text-slate-100">Run summary</div>
              <div className="mt-2 grid gap-2 text-sm text-slate-300">
                <div className="flex justify-between gap-4">
                  <span className="text-slate-400">Bench</span>
                  <span className="text-slate-200">
                    {benchMode === "use_existing"
                      ? (selectedBench?.name || "Existing bench") + ` (${selectedBenchId.slice(0, 8) || "—"})`
                      : (benchName.trim() || "New bench")}
                  </span>
                </div>
                <div className="flex justify-between gap-4">
                  <span className="text-slate-400">Instruments</span>
                  <span className="text-slate-200">
                    {benchMode === "use_existing" && !advancedOpen
                      ? "Use bench mapping (recommended)"
                      : `${selectedInstrumentIds.length} selected`}
                  </span>
                </div>
                <div className="flex justify-between gap-4">
                  <span className="text-slate-400">Test plan</span>
                  <span className="text-slate-200">
                    {planMode === "use_existing"
                      ? (selectedPlan?.name || "None selected")
                      : (testPlanName.trim() || "No name")}
                  </span>
                </div>
                <div className="flex justify-between gap-4">
                  <span className="text-slate-400">Apply proposal</span>
                  <span className="text-slate-200">{applyProposal ? "ON" : "OFF (recommended)"}</span>
                </div>
              </div>

              <div className="mt-4 text-xs text-slate-500">
                What happens: Generate handoff → bench setup (if needed) → preflight → hardware run → learn → proposals.
              </div>
            </div>

            <div className="mt-4 flex flex-wrap items-center gap-3">
              <button
                onClick={onRun}
                disabled={!canRun}
                className={cls(
                  "rounded-xl px-6 py-3 font-semibold transition",
                  canRun
                    ? "bg-cyan-600 hover:bg-cyan-500"
                    : "bg-slate-800 text-slate-400 cursor-not-allowed"
                )}
              >
                {running ? "Starting…" : "Run Validation"}
              </button>

              <button
                onClick={() => router.push("/workflow")}
                className="rounded-xl border border-slate-700 bg-slate-950/30 px-5 py-3 text-slate-200 hover:bg-slate-950 transition"
              >
                Open Studio (advanced)
              </button>

              <div className="text-xs text-slate-500">
                Recommended: do a first run with defaults before turning on “Apply.”
              </div>
            </div>

            {runErr ? (
              <div className="mt-4 rounded-xl border border-red-900/60 bg-red-500/10 p-4 text-sm text-red-200">
                {runErr}
              </div>
            ) : null}
          </div>
        </div>

        {/* Right: progress + logs */}
        <div className="lg:col-span-2 space-y-6">
          <div className="rounded-2xl border border-slate-800 bg-slate-900/15 p-6">
            <div className="flex items-start justify-between gap-3">
              <div>
                <div className="text-lg font-bold">Live progress</div>
                <div className="text-sm text-slate-400">
                  One parent run, but you’ll see every phase.
                </div>
              </div>
              <span className="rounded-full border border-slate-700 bg-slate-950/30 px-3 py-1 text-xs text-slate-200">
                Real-time
              </span>
            </div>

            <div className="mt-4 space-y-2">
              {PHASES.map((p) => {
                const s = phaseProgress[p.key] || "pending";
                const dot =
                  s === "done" ? "bg-cyan-400" :
                  s === "running" ? "bg-cyan-300 animate-pulse" :
                  s === "skipped" ? "bg-slate-500" :
                  "bg-slate-700";

                const label =
                  s === "done" ? "Done" :
                  s === "running" ? "Running" :
                  s === "skipped" ? "Skipped" :
                  "Pending";

                return (
                  <div key={p.key} className="flex items-center justify-between rounded-xl border border-slate-800 bg-black/30 px-4 py-3">
                    <div className="flex items-center gap-3">
                      <span className={cls("h-2.5 w-2.5 rounded-full", dot)} />
                      <div className="text-sm font-semibold text-slate-200">{p.key}</div>
                    </div>
                    <div className={cls(
                      "text-xs rounded-full px-2 py-1 border",
                      s === "done" ? "border-cyan-900/60 bg-cyan-500/10 text-cyan-200" :
                      s === "running" ? "border-cyan-900/60 bg-cyan-500/10 text-cyan-200" :
                      s === "skipped" ? "border-slate-700 bg-slate-950/20 text-slate-300" :
                      "border-slate-800 bg-slate-950/10 text-slate-400"
                    )}>
                      {label}
                    </div>
                  </div>
                );
              })}
            </div>

            <div className="mt-4 text-xs text-slate-500">
              Nudge: if preflight fails, it usually prevents a wasted hardware run.
            </div>

            {workflowId ? (
              <div className="mt-4 rounded-xl border border-slate-800 bg-black/30 p-4 text-xs text-slate-300">
                <div><span className="text-slate-500">workflow_id:</span> {workflowId}</div>
                {runId ? <div className="mt-1"><span className="text-slate-500">run_id:</span> {runId}</div> : null}
                {workflowRow?.status ? <div className="mt-1"><span className="text-slate-500">status:</span> {workflowRow.status}</div> : null}
                {workflowRow?.phase ? <div className="mt-1"><span className="text-slate-500">phase:</span> {workflowRow.phase}</div> : null}
              </div>
            ) : (
              <div className="mt-4 rounded-xl border border-slate-800 bg-black/20 p-4 text-sm text-slate-400">
                Start a run to see progress here.
              </div>
            )}
          </div>

          <div className="rounded-2xl border border-slate-800 bg-slate-900/15 p-6">
            <div className="flex items-start justify-between gap-3">
              <div>
                <div className="text-lg font-bold">Run log</div>
                <div className="text-sm text-slate-400">
                  Streaming logs from the parent workflow.
                </div>
              </div>
              <button
                onClick={() => {
                  if (logsRef.current) logsRef.current.scrollTop = logsRef.current.scrollHeight;
                }}
                className="rounded-xl border border-slate-700 bg-slate-950/30 px-3 py-2 text-xs hover:bg-slate-950 transition"
              >
                Jump to end
              </button>
            </div>

            <div
              ref={logsRef}
              className="mt-4 h-[420px] overflow-auto rounded-2xl border border-slate-800 bg-black/40 p-4 text-xs text-slate-200"
            >
              {loading ? (
                <div className="text-slate-400">Loading…</div>
              ) : workflowId && logLines.length === 0 ? (
                <div className="text-slate-400">Run started. Waiting for logs…</div>
              ) : logLines.length === 0 ? (
                <div className="text-slate-500">
                  Tip: start with the recommended defaults for a clean first run.
                </div>
              ) : (
                <div className="space-y-1">
                  {logLines.map((l, i) => (
                    <div key={i} className="whitespace-pre-wrap break-words">
                      {l}
                    </div>
                  ))}
                </div>
              )}
            </div>

            <div className="mt-3 text-xs text-slate-500">
              Nudge: after your first successful run, reuse the same bench + test plan for iteration-2+.
            </div>
          </div>
        </div>
      </section>

      <style jsx>{`
        @media (prefers-reduced-motion: reduce) {
          .animate-pulse {
            animation: none;
          }
        }
      `}</style>
    </main>
  );
}
