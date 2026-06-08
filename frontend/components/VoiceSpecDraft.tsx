"use client";

import { useRef, useState } from "react";
import { useRouter } from "next/navigation";
import { FiMic } from "react-icons/fi";
import { createClientComponentClient } from "@/lib/platformClient";

type VoiceNote = {
  id: string;
  transcript: string;
};

type VoiceSpecDraftProps = {
  title?: string;
  subtitle?: string;
  loopType?: string;
  target?: string;
  compact?: boolean;
  inline?: boolean;
  onApply: (draft: string) => void;
};

type TrialCheckoutPrompt = {
  message: string;
  checkoutUrl: string;
  checkoutLabel: string;
};

function makeId(): string {
  if (typeof crypto !== "undefined" && "randomUUID" in crypto) return crypto.randomUUID();
  return `voice-${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

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

function trialCheckoutPrompt(data: unknown): TrialCheckoutPrompt | null {
  const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
  const detail = responseObject && "detail" in responseObject ? responseObject.detail : data;
  const detailObject = detail && typeof detail === "object" ? (detail as Record<string, unknown>) : null;
  if (!detailObject || detailObject.requires_checkout !== true) return null;
  return {
    message:
      typeof detailObject.message === "string"
        ? detailObject.message
        : "Start your 3-day trial to use voice design sessions.",
    checkoutUrl: typeof detailObject.checkout_url === "string" ? detailObject.checkout_url : "/pricing?trial=1",
    checkoutLabel: typeof detailObject.checkout_label === "string" ? detailObject.checkout_label : "Start 3-day trial",
  };
}

export default function VoiceSpecDraft({
  title = "Voice Design Session",
  subtitle = "Speak short notes. ChipLoop transcribes them, drafts a spec, and lets you review before running.",
  loopType = "digital",
  target = "ChipLoop App",
  compact = false,
  inline = false,
  onApply,
}: VoiceSpecDraftProps) {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const [open, setOpen] = useState(false);
  const [recording, setRecording] = useState(false);
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [trialPrompt, setTrialPrompt] = useState<TrialCheckoutPrompt | null>(null);
  const [notes, setNotes] = useState<VoiceNote[]>([]);
  const recorderRef = useRef<MediaRecorder | null>(null);

  async function authHeaders(): Promise<Record<string, string>> {
    const {
      data: { session },
    } = await supabase.auth.getSession();
    return session?.access_token ? { Authorization: `Bearer ${session.access_token}` } : {};
  }

  async function startStopRecording() {
    setError(null);
    setTrialPrompt(null);
    if (recording && recorderRef.current) {
      recorderRef.current.stop();
      setRecording(false);
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

      recorder.ondataavailable = (event) => {
        if (event.data.size > 0) chunks.push(event.data);
      };
      recorder.onstop = async () => {
        stream.getTracks().forEach((track) => track.stop());
        recorderRef.current = null;
        setBusy(true);
        try {
          const form = new FormData();
          form.append("file", new Blob(chunks, { type: "audio/webm" }), `voice-note-${Date.now()}.webm`);
          const response = await fetch("/api/studio/voice/transcribe", {
            method: "POST",
            headers: await authHeaders(),
            body: form,
            cache: "no-store",
          });
          const data = await parseResponse(response);
          if (!response.ok) {
            const prompt = trialCheckoutPrompt(data);
            if (prompt) {
              setTrialPrompt(prompt);
              throw new Error(prompt.message);
            }
            throw new Error(errorMessage(data, `Transcription failed with status ${response.status}.`));
          }
          const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
          const transcript = String(responseObject?.transcript || "").trim();
          if (!transcript) throw new Error("No transcript returned.");
          setNotes((current) => current.concat({ id: makeId(), transcript }));
        } catch (err) {
          setError(err instanceof Error ? err.message : "Voice transcription failed.");
        } finally {
          setBusy(false);
        }
      };

      recorder.start();
      recorderRef.current = recorder;
      setRecording(true);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Microphone permission was not granted.");
      setRecording(false);
    }
  }

  async function generateSpec() {
    if (!notes.length) return;
    setError(null);
    setTrialPrompt(null);
    setBusy(true);
    try {
      const response = await fetch("/api/studio/voice/spec-draft", {
        method: "POST",
        headers: { "Content-Type": "application/json", ...(await authHeaders()) },
        body: JSON.stringify({
          transcripts: notes.map((note) => note.transcript),
          loop_type: loopType,
          target,
        }),
        cache: "no-store",
      });
      const data = await parseResponse(response);
      if (!response.ok) {
        const prompt = trialCheckoutPrompt(data);
        if (prompt) {
          setTrialPrompt(prompt);
          throw new Error(prompt.message);
        }
        throw new Error(errorMessage(data, `Spec draft failed with status ${response.status}.`));
      }
      const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
      const draft = String(responseObject?.spec_draft || "").trim();
      if (!draft) throw new Error("No spec draft returned.");
      onApply(draft);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Spec draft generation failed.");
    } finally {
      setBusy(false);
    }
  }

  return (
    <div className={inline ? "relative inline-flex flex-col items-end" : `rounded-2xl border border-cyan-900/50 bg-cyan-950/15 ${compact ? "p-2" : "p-4"}`}>
      <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
        <div className={compact ? "sr-only" : ""}>
          <div className="text-sm font-semibold text-cyan-200">{title}</div>
          <div className="mt-1 text-xs leading-5 text-slate-400">{subtitle}</div>
        </div>
        <button
          type="button"
          onClick={() => setOpen((current) => !current)}
          title={open ? "Hide voice input" : "Use voice input"}
          className={inline ? "inline-flex h-9 w-9 items-center justify-center rounded-lg border border-cyan-800 bg-cyan-950/30 text-cyan-100 transition hover:bg-cyan-900/40" : compact ? "inline-flex items-center rounded-lg border border-cyan-800 px-3 py-2 text-sm font-semibold text-cyan-100 transition hover:bg-cyan-900/30" : "rounded-lg border border-cyan-800 px-3 py-2 text-xs font-semibold text-cyan-100 transition hover:bg-cyan-900/30"}
        >
          {compact ? (
            <>
              <FiMic aria-hidden="true" />
              <span className="sr-only">{open ? "Hide voice input" : "Use voice input"}</span>
            </>
          ) : open ? "Hide Voice" : "Use Voice"}
        </button>
      </div>

      {open ? (
        <div className={inline ? "absolute bottom-11 right-0 z-20 w-[min(420px,80vw)] space-y-3 rounded-xl border border-cyan-900/70 bg-slate-950 p-3 shadow-2xl" : "mt-4 space-y-3"}>
          <div className="flex flex-wrap gap-2">
            <button
              type="button"
              onClick={startStopRecording}
              disabled={busy}
              className={`rounded-lg px-4 py-2 text-sm font-semibold transition ${
                recording ? "bg-red-600 text-white hover:bg-red-500" : "bg-cyan-600 text-white hover:bg-cyan-500"
              } disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500`}
            >
              {recording ? "Stop Recording" : busy ? "Processing..." : "Record Voice Note"}
            </button>
            <button
              type="button"
              onClick={generateSpec}
              disabled={!notes.length || busy || recording}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
            >
              Generate Spec
            </button>
            <button
              type="button"
              onClick={() => {
                setNotes([]);
                setError(null);
                setTrialPrompt(null);
              }}
              disabled={!notes.length || busy || recording}
              className="rounded-lg px-4 py-2 text-sm text-slate-400 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-600"
            >
              Clear
            </button>
          </div>

          {error ? (
            <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-xs text-red-200">
              <div>{error}</div>
              {trialPrompt ? (
                <button
                  type="button"
                  onClick={() => router.push(trialPrompt.checkoutUrl)}
                  className="mt-3 rounded-lg bg-cyan-600 px-3 py-2 text-xs font-semibold text-white transition hover:bg-cyan-500"
                >
                  {trialPrompt.checkoutLabel}
                </button>
              ) : null}
            </div>
          ) : null}

          <div className="max-h-44 space-y-2 overflow-auto">
            {notes.length ? notes.map((note, index) => (
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
  );
}
