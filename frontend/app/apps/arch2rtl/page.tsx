"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { apiPost } from "@/lib/apiClient";

const supabase = createClientComponentClient();
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "http://localhost:8000";
const ONBOARDING_DEMO_KEY = "chiploop_arch2rtl_onboarding_demo";

const ARCH2RTL_ONBOARDING_SPEC = `Design a parameterized PWM controller.

Inputs:
- clk
- reset_n
- enable
- duty_cycle[7:0]
- period[7:0]

Outputs:
- pwm_out
- counter_value[7:0]

Behavior:
- Counter increments every clock when enable is high.
- Counter resets to zero when it reaches period.
- pwm_out is high when counter_value is less than duty_cycle.
- All registers reset to zero when reset_n is low.

Generate synthesizable SystemVerilog, timing constraints, UPF-lite power intent, and a handoff package.`;

const ARCH2RTL_ONBOARDING_DEFAULTS = {
  projectName: "pwm_controller_onboarding",
  topModule: "pwm_controller",
  designLanguage: "systemverilog" as const,
  specText: ARCH2RTL_ONBOARDING_SPEC,
  toggles: { genRegmap: true, genUpfLite: true, genPackaging: true },
};

type WorkflowRow = {
  id: string;
  status?: string | null;
  phase?: string | null;
  logs?: string | null;
  updated_at?: string | null;
};

type VoiceNote = {
  id: string;
  transcript: string;
};

function parseLogLines(logs: string | null | undefined): string[] {
  if (!logs) return [];
  return logs.split("\n").map(l => l.trimEnd()).filter(l => l.trim().length > 0);
}

export default function Arch2RTLAppPage() {
  const router = useRouter();

  const [sessionUserId, setSessionUserId] = useState<string | null>(null);
  const [accessToken, setAccessToken] = useState<string | null>(null);

  const [loading, setLoading] = useState(true);
  const [running, setRunning] = useState(false);
  const [err, setErr] = useState<string | null>(null);

  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runId, setRunId] = useState<string | null>(null);
  const [workflowRow, setWorkflowRow] = useState<WorkflowRow | null>(null);
  const [guidedOnboarding, setGuidedOnboarding] = useState(false);
  const [onboardingCompleted, setOnboardingCompleted] = useState(false);

  // Intake
  const [projectName, setProjectName] = useState("");
  const [topModule, setTopModule] = useState("");
  const [designLanguage, setDesignLanguage] = useState<"systemverilog" | "verilog">("systemverilog");
  const [specText, setSpecText] = useState("");

  const [genRegmap, setGenRegmap] = useState(true);
  const [genUpfLite, setGenUpfLite] = useState(false);
  const [genPackaging, setGenPackaging] = useState(true);
  const [voiceOpen, setVoiceOpen] = useState(false);
  const [voiceRecording, setVoiceRecording] = useState(false);
  const [voiceBusy, setVoiceBusy] = useState(false);
  const [voiceErr, setVoiceErr] = useState<string | null>(null);
  const [voiceNotes, setVoiceNotes] = useState<VoiceNote[]>([]);
  const mediaRecorderRef = useRef<MediaRecorder | null>(null);

  const logLines = useMemo(() => parseLogLines(workflowRow?.logs), [workflowRow?.logs]);
  const logsRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    if (!logsRef.current) return;
    logsRef.current.scrollTop = logsRef.current.scrollHeight;
  }, [logLines.length]);

  function authHeaders(): HeadersInit {
    const h: Record<string, string> = {};
    if (sessionUserId) h["x-user-id"] = sessionUserId;
    if (accessToken) h["Authorization"] = `Bearer ${accessToken}`;
    return h;
  }

  async function postJSON<T>(path: string, body: unknown): Promise<T> {
    const resp = await fetch(`${API_BASE}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json", ...authHeaders() },
      body: JSON.stringify(body),
    });
    if (!resp.ok) {
      const txt = await resp.text().catch(() => "");
      throw new Error(`${resp.status} ${resp.statusText}${txt ? ` - ${txt}` : ""}`);
    }
    return resp.json();
  }

  async function postVoiceForm<T>(path: string, body: FormData): Promise<T> {
    const headers: Record<string, string> = {};
    if (accessToken) headers["Authorization"] = `Bearer ${accessToken}`;
    const resp = await fetch(`/api${path}`, {
      method: "POST",
      headers,
      body,
      cache: "no-store",
    });
    const text = await resp.text();
    const data = text ? JSON.parse(text) : null;
    if (!resp.ok) {
      const detail = data?.detail ?? data;
      const message =
        typeof detail === "string"
          ? detail
          : typeof detail?.message === "string"
          ? detail.message
          : `Voice request failed with status ${resp.status}`;
      throw new Error(message);
    }
    return data as T;
  }

  async function postVoiceJSON<T>(path: string, body: unknown): Promise<T> {
    const headers: Record<string, string> = { "Content-Type": "application/json" };
    if (accessToken) headers["Authorization"] = `Bearer ${accessToken}`;
    const resp = await fetch(`/api${path}`, {
      method: "POST",
      headers,
      body: JSON.stringify(body),
      cache: "no-store",
    });
    const text = await resp.text();
    const data = text ? JSON.parse(text) : null;
    if (!resp.ok) {
      const detail = data?.detail ?? data;
      const message =
        typeof detail === "string"
          ? detail
          : typeof detail?.message === "string"
          ? detail.message
          : `Voice request failed with status ${resp.status}`;
      throw new Error(message);
    }
    return data as T;
  }

  // Auth gate
  useEffect(() => {
    (async () => {
      setLoading(true);
      setErr(null);
      const { data: { session } } = await supabase.auth.getSession();
      if (!session?.user) {
        const next = typeof window !== "undefined"
          ? `${window.location.pathname}${window.location.search}`
          : "/apps/arch2rtl";
        router.replace(`/login?next=${encodeURIComponent(next)}`);
        return;
      }
      setSessionUserId(session.user.id);
      setAccessToken(session.access_token);
      setLoading(false);
    })();
  }, [router]);

  useEffect(() => {
    if (loading || typeof window === "undefined") return;
    const guided = new URLSearchParams(window.location.search).get("guided") === "1";
    if (!guided) return;

    setGuidedOnboarding(true);
    let demo = ARCH2RTL_ONBOARDING_DEFAULTS;
    const raw = window.localStorage.getItem(ONBOARDING_DEMO_KEY);

    if (raw) {
      try {
        const parsed = JSON.parse(raw) as Partial<typeof ARCH2RTL_ONBOARDING_DEFAULTS>;
        demo = {
          ...ARCH2RTL_ONBOARDING_DEFAULTS,
          ...parsed,
          toggles: { ...ARCH2RTL_ONBOARDING_DEFAULTS.toggles, ...parsed.toggles },
        };
      } catch {
        window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
      }
    }

    setProjectName(demo.projectName);
    setTopModule(demo.topModule);
    setDesignLanguage(demo.designLanguage);
    setSpecText(demo.specText);
    setGenRegmap(demo.toggles.genRegmap);
    setGenUpfLite(demo.toggles.genUpfLite);
    setGenPackaging(demo.toggles.genPackaging);
  }, [loading]);

  // Live workflow updates
  useEffect(() => {
    if (!workflowId) return;

    let isActive = true;

    (async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("id,status,phase,logs,updated_at")
        .eq("id", workflowId)
        .single();

      if (isActive && !error && data) setWorkflowRow(data as WorkflowRow);
    })();

    const channel = supabase
      .channel(`wf-${workflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
        (payload) => {
          const row = payload.new as Partial<WorkflowRow>;
          setWorkflowRow({
            id: row.id || workflowId,
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

  const canRun = useMemo(() => {
    if (running) return false;
    if (!specText.trim()) return false;
    if (!topModule.trim()) return false;
    return true;
  }, [running, specText, topModule]);

  async function startStopVoiceRecording() {
    setVoiceErr(null);
    if (voiceRecording && mediaRecorderRef.current) {
      mediaRecorderRef.current.stop();
      setVoiceRecording(false);
      return;
    }
    if (!navigator.mediaDevices?.getUserMedia || typeof MediaRecorder === "undefined") {
      setVoiceErr("Voice recording is not supported in this browser.");
      return;
    }

    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      const recorder = new MediaRecorder(stream);
      const chunks: BlobPart[] = [];

      recorder.ondataavailable = (event) => {
        if (event.data.size > 0) chunks.push(event.data);
      };
      recorder.onstop = async () => {
        stream.getTracks().forEach((track) => track.stop());
        mediaRecorderRef.current = null;
        setVoiceBusy(true);
        try {
          const blob = new Blob(chunks, { type: "audio/webm" });
          const form = new FormData();
          form.append("file", blob, `voice-note-${Date.now()}.webm`);
          const result = await postVoiceForm<{ transcript?: string }>("/studio/voice/transcribe", form);
          const transcript = (result.transcript || "").trim();
          if (!transcript) throw new Error("No transcript returned.");
          setVoiceNotes((current) => current.concat({ id: crypto.randomUUID(), transcript }));
        } catch (error) {
          setVoiceErr(error instanceof Error ? error.message : "Voice transcription failed.");
        } finally {
          setVoiceBusy(false);
        }
      };

      recorder.start();
      mediaRecorderRef.current = recorder;
      setVoiceRecording(true);
    } catch (error) {
      setVoiceErr(error instanceof Error ? error.message : "Microphone permission was not granted.");
      setVoiceRecording(false);
    }
  }

  async function generateSpecFromVoice() {
    if (!voiceNotes.length) return;
    setVoiceErr(null);
    setVoiceBusy(true);
    try {
      const result = await postVoiceJSON<{ spec_draft?: string }>("/studio/voice/spec-draft", {
        transcripts: voiceNotes.map((note) => note.transcript),
        loop_type: "digital",
        target: "Arch2RTL",
      });
      const draft = (result.spec_draft || "").trim();
      if (!draft) throw new Error("No spec draft returned.");
      setSpecText(draft);
      if (!topModule.trim()) {
        const moduleMatch = draft.match(/(?:top module|module|block name)\s*[:\-]\s*([a-zA-Z_][a-zA-Z0-9_]*)/i);
        if (moduleMatch?.[1]) setTopModule(moduleMatch[1]);
      }
    } catch (error) {
      setVoiceErr(error instanceof Error ? error.message : "Spec draft generation failed.");
    } finally {
      setVoiceBusy(false);
    }
  }

  async function runNow() {
    setErr(null);
    setRunning(true);
    try {
      const out = await postJSON<{ ok: boolean; workflow_id: string; run_id: string }>(
        "/apps/arch2rtl/run",
        {
          project_name: projectName || undefined,
          top_module: topModule,
          design_language: designLanguage,
          spec_text: specText,
          toggles: {
            gen_regmap: genRegmap,
            gen_upf_lite: genUpfLite,
            gen_packaging: genPackaging,
          },
        }
      );
      setWorkflowId(out.workflow_id);
      setRunId(out.run_id);
      if (guidedOnboarding) {
        apiPost("/settings/onboarding", {
          action: "start",
          last_step: "arch2rtl_workflow_started",
          workflow_id: out.workflow_id,
          metadata: { demo: "arch2rtl" },
        }).catch(() => undefined);
      }
    } catch (e: unknown) {
      setErr(e instanceof Error ? e.message : String(e));
    } finally {
      setRunning(false);
    }
  }

  async function downloadZip() {
    if (!workflowId) return;
    window.open(`${API_BASE}/workflow/${workflowId}/download_zip?full=1`, "_blank");
    if (guidedOnboarding) {
      try {
        await apiPost("/settings/onboarding", {
          action: "complete",
          workflow_id: workflowId,
          last_step: "downloaded_artifacts",
          metadata: { demo: "arch2rtl", reviewed_files: ["rtl/*.sv", "constraints/*.sdc", "power/*.upf"] },
        });
        setOnboardingCompleted(true);
        window.localStorage.removeItem(ONBOARDING_DEMO_KEY);
      } catch {
        setOnboardingCompleted(true);
      }
    }
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-black text-white flex items-center justify-center">
        <div className="text-slate-300">Loading...</div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-6xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900">
            Studio
          </button>
        </div>

        {guidedOnboarding ? (
          <div className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/20 p-5">
            <div className="flex flex-wrap items-start justify-between gap-4">
              <div>
                <div className="text-sm font-semibold uppercase tracking-wide text-cyan-300">Guided first activity</div>
                <h2 className="mt-1 text-2xl font-bold text-white">Run Arch2RTL and inspect the handoff package</h2>
                <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                  The PWM controller spec is already filled in. Click Run Arch2RTL, wait for logs to finish, then download the ZIP and inspect the RTL, SDC, and UPF files.
                </p>
              </div>
              {onboardingCompleted ? (
                <span className="rounded-full border border-emerald-700 bg-emerald-950/40 px-3 py-1 text-sm text-emerald-100">
                  Completed
                </span>
              ) : null}
            </div>
            <div className="mt-4 grid gap-3 md:grid-cols-4">
              {[
                "Review pre-filled PWM spec",
                "Run Arch2RTL",
                "Open the downloaded RTL, SDC, and UPF files",
                "Download ZIP to complete onboarding",
              ].map((item, idx) => (
                <div key={item} className="rounded-xl border border-slate-800 bg-black/25 p-3 text-sm text-slate-200">
                  <div className="mb-2 flex h-7 w-7 items-center justify-center rounded-full bg-cyan-600 text-xs font-bold">{idx + 1}</div>
                  {item}
                </div>
              ))}
            </div>
          </div>
        ) : null}

        <div className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Digital Loop</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">Arch2RTL</h1>
          <p className="mt-2 text-slate-300">One-shot intake to one click run to progressive outputs to ZIP handoff.</p>

          <div className="mt-6 grid gap-4 md:grid-cols-2">
            <div className="space-y-3">
              <label className="block text-sm text-slate-300">Project name (optional)</label>
              <input value={projectName} onChange={e => setProjectName(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Top module *</label>
              <input value={topModule} onChange={e => setTopModule(e.target.value)}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100" />

              <label className="block text-sm text-slate-300">Design language</label>
              <select value={designLanguage} onChange={e => setDesignLanguage(e.target.value as "systemverilog" | "verilog")}
                className="w-full rounded-xl border border-slate-800 bg-black/30 px-4 py-2 text-slate-100">
                <option value="systemverilog">SystemVerilog</option>
                <option value="verilog">Verilog</option>
              </select>

              <div className="mt-3 space-y-2">
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genRegmap} onChange={e => setGenRegmap(e.target.checked)} />
                  Generate regmap
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genUpfLite} onChange={e => setGenUpfLite(e.target.checked)} />
                  Generate UPF-lite
                </label>
                <label className="flex items-center gap-2 text-sm text-slate-300">
                  <input type="checkbox" checked={genPackaging} onChange={e => setGenPackaging(e.target.checked)} />
                  Generate packaging/handoff
                </label>
              </div>

              <button
                onClick={runNow}
                disabled={!canRun}
                className={`mt-4 w-full rounded-xl px-5 py-3 font-semibold transition ${
                  canRun ? "bg-cyan-600 hover:bg-cyan-500" : "bg-slate-700 cursor-not-allowed"
                }`}
              >
                {running ? "Starting..." : "Run Arch2RTL"}
              </button>

              {err ? <div className="mt-3 text-sm text-red-300">{err}</div> : null}

              {workflowId ? (
                <div className="mt-4 rounded-xl border border-slate-800 bg-black/30 p-4 text-sm text-slate-300">
                  <div>workflow_id: <span className="text-slate-100">{workflowId}</span></div>
                  <div>run_id: <span className="text-slate-100">{runId}</span></div>
                  <button onClick={downloadZip} className="mt-3 rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700">
                    {guidedOnboarding ? "Download ZIP and finish" : "Download ZIP (full=1)"}
                  </button>
                </div>
              ) : null}
            </div>

            <div>
              <div className="mb-4 rounded-2xl border border-cyan-900/50 bg-cyan-950/15 p-4">
                <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
                  <div>
                    <div className="text-sm font-semibold text-cyan-200">Voice Design Session</div>
                    <div className="mt-1 text-xs leading-5 text-slate-400">
                      Speak your design idea in short notes. ChipLoop transcribes them, then drafts a spec you can edit before running.
                    </div>
                  </div>
                  <button
                    type="button"
                    onClick={() => setVoiceOpen((current) => !current)}
                    className="rounded-lg border border-cyan-800 px-3 py-2 text-xs font-semibold text-cyan-100 transition hover:bg-cyan-900/30"
                  >
                    {voiceOpen ? "Hide Voice" : "Use Voice"}
                  </button>
                </div>

                {voiceOpen ? (
                  <div className="mt-4 space-y-3">
                    <div className="flex flex-wrap gap-2">
                      <button
                        type="button"
                        onClick={startStopVoiceRecording}
                        disabled={voiceBusy}
                        className={`rounded-lg px-4 py-2 text-sm font-semibold transition ${
                          voiceRecording
                            ? "bg-red-600 text-white hover:bg-red-500"
                            : "bg-cyan-600 text-white hover:bg-cyan-500"
                        } disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500`}
                      >
                        {voiceRecording ? "Stop Recording" : voiceBusy ? "Processing..." : "Record Voice Note"}
                      </button>
                      <button
                        type="button"
                        onClick={generateSpecFromVoice}
                        disabled={!voiceNotes.length || voiceBusy || voiceRecording}
                        className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                      >
                        Generate Spec
                      </button>
                      <button
                        type="button"
                        onClick={() => {
                          setVoiceNotes([]);
                          setVoiceErr(null);
                        }}
                        disabled={!voiceNotes.length || voiceBusy || voiceRecording}
                        className="rounded-lg px-4 py-2 text-sm text-slate-400 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-600"
                      >
                        Clear
                      </button>
                    </div>

                    {voiceErr ? <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-xs text-red-200">{voiceErr}</div> : null}

                    <div className="max-h-44 space-y-2 overflow-auto">
                      {voiceNotes.length ? voiceNotes.map((note, index) => (
                        <div key={note.id} className="rounded-xl border border-slate-800 bg-black/25 p-3 text-xs leading-5 text-slate-200">
                          <div className="mb-1 font-semibold text-cyan-200">Voice note {index + 1}</div>
                          {note.transcript}
                        </div>
                      )) : (
                        <div className="rounded-xl border border-slate-800 bg-black/20 p-3 text-xs text-slate-500">
                          No voice notes yet. Record one or more short notes, then generate a spec draft.
                        </div>
                      )}
                    </div>
                  </div>
                ) : null}
              </div>

              <label className="block text-sm text-slate-300">Spec text *</label>
              <textarea
                value={specText}
                onChange={e => setSpecText(e.target.value)}
                rows={18}
                className="mt-2 w-full rounded-2xl border border-slate-800 bg-black/30 p-4 text-slate-100"
                placeholder="Paste your spec here..."
              />
              <div className="mt-2 text-xs text-slate-500">Tip: keep it structured (interfaces, clocks, resets, targets).</div>
            </div>
          </div>

          <div className="mt-6 rounded-2xl border border-slate-800 bg-black/20 p-4">
            <div className="text-sm font-semibold">Live logs</div>
            <div ref={logsRef} className="mt-3 max-h-[320px] overflow-auto rounded-xl border border-slate-800 bg-black/30 p-3 text-xs text-slate-200">
              {logLines.length ? logLines.map((l, i) => <div key={i} className="whitespace-pre-wrap">{l}</div>) : (
                <div className="text-slate-500">No logs yet. Click Run Arch2RTL.</div>
              )}
            </div>
          </div>
        </div>
      </div>
    </main>
  );
}





