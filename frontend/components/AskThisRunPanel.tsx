"use client";

import { FormEvent, useEffect, useMemo, useRef, useState } from "react";
import { FiMic } from "react-icons/fi";
import { createClientComponentClient } from "@/lib/platformClient";
import { apiPost } from "@/lib/apiClient";

type AskThisRunResponse = {
  workflow_id: string;
  question: string;
  answer: string;
  sources?: Array<{ type: string; path: string }>;
  source_count?: number;
};

type Props = {
  workflowId: string | null | undefined;
  compact?: boolean;
};

const suggestions = [
  "Summarize this run and the key artifacts.",
  "What should I inspect first?",
  "Are there warnings, failures, or missing outputs?",
  "What is the recommended next step?",
];

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

export default function AskThisRunPanel({ workflowId, compact = false }: Props) {
  const supabase = useMemo(() => createClientComponentClient(), []);
  const [status, setStatus] = useState<string | null>(null);
  const [question, setQuestion] = useState("");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [history, setHistory] = useState<AskThisRunResponse[]>([]);
  const [voiceRecording, setVoiceRecording] = useState(false);
  const [voiceBusy, setVoiceBusy] = useState(false);
  const [voiceStatus, setVoiceStatus] = useState<string | null>(null);
  const voiceRecorderRef = useRef<MediaRecorder | null>(null);
  const voiceStreamRef = useRef<MediaStream | null>(null);

  useEffect(() => {
    if (!workflowId) {
      setStatus(null);
      return;
    }

    let active = true;

    (async () => {
      const { data } = await supabase
        .from("workflows")
        .select("status")
        .eq("id", workflowId)
        .maybeSingle<{ status?: string | null }>();
      if (active) setStatus(data?.status || null);
    })();

    const channel = supabase
      .channel(`ask-this-run-${workflowId}`)
      .on(
        "postgres_changes",
        { event: "*", schema: "public", table: "workflows", filter: `id=eq.${workflowId}` },
        (payload) => {
          const row = payload.new as { status?: string | null };
          setStatus(row.status || null);
        }
      )
      .subscribe();

    return () => {
      active = false;
      supabase.removeChannel(channel);
    };
  }, [supabase, workflowId]);

  useEffect(() => {
    return () => {
      const recorder = voiceRecorderRef.current;
      if (recorder && recorder.state !== "inactive") {
        recorder.onstop = null;
        recorder.stop();
      }
      stopVoiceTracks();
    };
  }, []);

  function stopVoiceTracks() {
    voiceStreamRef.current?.getTracks().forEach((track) => track.stop());
    voiceStreamRef.current = null;
  }

  async function authHeaders(): Promise<Record<string, string>> {
    const {
      data: { session },
    } = await supabase.auth.getSession();
    return session?.access_token ? { Authorization: `Bearer ${session.access_token}` } : {};
  }

  async function toggleVoiceRecording() {
    setError(null);
    setVoiceStatus(null);

    const activeRecorder = voiceRecorderRef.current;
    if (voiceRecording && activeRecorder && activeRecorder.state !== "inactive") {
      activeRecorder.stop();
      setVoiceRecording(false);
      return;
    }

    if (!navigator.mediaDevices?.getUserMedia || typeof MediaRecorder === "undefined") {
      setError("Voice recording is not supported in this browser.");
      return;
    }

    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      const recorder = new MediaRecorder(stream);
      const chunks: BlobPart[] = [];
      voiceStreamRef.current = stream;

      recorder.ondataavailable = (event) => {
        if (event.data.size > 0) chunks.push(event.data);
      };

      recorder.onstop = async () => {
        stopVoiceTracks();
        voiceRecorderRef.current = null;
        setVoiceBusy(true);
        try {
          const form = new FormData();
          form.append("file", new Blob(chunks, { type: "audio/webm" }), `ask-this-run-${Date.now()}.webm`);
          const response = await fetch("/api/studio/voice/transcribe", {
            method: "POST",
            headers: await authHeaders(),
            body: form,
            cache: "no-store",
          });
          const data = await parseResponse(response);
          if (!response.ok) throw new Error(errorMessage(data, `Transcription failed with status ${response.status}.`));
          const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
          const transcript = String(responseObject?.transcript || "").trim();
          if (!transcript) throw new Error("No transcript returned.");
          setQuestion((current) => [current.trim(), transcript].filter(Boolean).join("\n\n"));
          setVoiceStatus("Transcript added.");
        } catch (err) {
          setError(err instanceof Error ? err.message : "Voice transcription failed.");
        } finally {
          setVoiceBusy(false);
        }
      };

      recorder.start();
      voiceRecorderRef.current = recorder;
      setVoiceRecording(true);
    } catch (err) {
      stopVoiceTracks();
      setVoiceRecording(false);
      setError(err instanceof Error ? err.message : "Microphone permission was not granted.");
    }
  }

  async function ask(questionOverride?: string) {
    const text = (questionOverride || question).trim();
    if (!workflowId || !text || loading) return;
    setLoading(true);
    setError(null);
    try {
      const response = await apiPost<AskThisRunResponse>(`/workflow/${workflowId}/ask`, { question: text });
      setHistory((current) => [response, ...current].slice(0, 10));
      setQuestion("");
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "Ask This Run failed.");
    } finally {
      setLoading(false);
    }
  }

  function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    ask();
  }

  const normalizedStatus = (status || "").toLowerCase();
  const finished = ["completed", "complete", "success", "succeeded", "failed", "error", "cancelled", "canceled"].includes(normalizedStatus);

  if (!workflowId || !finished) return null;

  return (
    <div className={`w-full rounded-xl border border-cyan-900/60 bg-cyan-950/20 ${compact ? "p-4" : "p-5"}`}>
      <div className="font-semibold text-cyan-200">Ask This Run</div>
      <p className="mt-1 text-sm leading-6 text-cyan-100/80">
        Ask questions about this run&apos;s logs, generated files, reports, warnings, and next steps.
      </p>

      <div className="mt-3 flex flex-wrap gap-2">
        {suggestions.map((suggestion) => (
          <button
            key={suggestion}
            type="button"
            disabled={loading}
            onClick={() => ask(suggestion)}
            className="rounded border border-cyan-700 px-3 py-1 text-xs text-cyan-100 hover:bg-cyan-900/40 disabled:cursor-not-allowed disabled:opacity-50"
          >
            {suggestion}
          </button>
        ))}
      </div>

      <form onSubmit={submit} className="mt-3 space-y-3">
        <textarea
          value={question}
          onChange={(event) => setQuestion(event.target.value)}
          placeholder="Ask about failures, warnings, generated files, coverage, handoff readiness..."
          className="min-h-20 w-full rounded-lg border border-slate-700 bg-slate-950 p-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
        />
        <div className="flex flex-wrap items-center gap-2">
          <button
            type="submit"
            disabled={loading || question.trim().length < 3}
            className="rounded bg-cyan-700 px-4 py-2 text-sm font-semibold text-white hover:bg-cyan-600 disabled:cursor-not-allowed disabled:bg-slate-700"
          >
            {loading ? "Inspecting..." : "Ask this run"}
          </button>
          <button
            type="button"
            disabled={voiceBusy}
            onClick={toggleVoiceRecording}
            title={voiceRecording ? "Stop voice recording" : "Use voice input"}
            className={`inline-flex h-10 w-10 items-center justify-center rounded-lg border transition disabled:cursor-not-allowed disabled:opacity-50 ${
              voiceRecording
                ? "border-red-500 bg-red-950/40 text-red-100 hover:bg-red-900/50"
                : "border-cyan-800 bg-cyan-950/30 text-cyan-100 hover:bg-cyan-900/40"
            }`}
          >
            <FiMic aria-hidden="true" />
            <span className="sr-only">{voiceRecording ? "Stop voice recording" : "Use voice input"}</span>
          </button>
          {voiceBusy ? <span className="text-xs text-cyan-200">Transcribing...</span> : null}
          {voiceStatus ? <span className="text-xs text-cyan-200">{voiceStatus}</span> : null}
        </div>
      </form>

      {error ? (
        <div className="mt-3 rounded border border-red-800 bg-red-950/40 p-3 text-sm text-red-200">{error}</div>
      ) : null}

      <div className="mt-4 space-y-3">
        {history.map((item, index) => (
          <div key={`${item.question}-${index}`} className="rounded-lg border border-slate-700 bg-slate-900/50 p-4">
            <div className="text-xs font-semibold uppercase tracking-wide text-slate-400">Question</div>
            <div className="mt-1 text-slate-100">{item.question}</div>
            <div className="mt-4 text-xs font-semibold uppercase tracking-wide text-cyan-300">Answer</div>
            <div className="mt-2 whitespace-pre-wrap leading-6 text-slate-200">{item.answer}</div>
            {item.sources?.length ? (
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
}
