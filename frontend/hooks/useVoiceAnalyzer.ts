import { useState, useEffect } from "react";

export function useVoiceAnalyzer() {
  const [isRecording, setIsRecording] = useState(false);
  const [summary, setSummary] = useState<any>(null);
  const [coverage, setCoverage] = useState(0);
  const [recorder, setRecorder] = useState<MediaRecorder | null>(null);

  async function startStopRecording() {
    if (isRecording && recorder) {
      recorder.stop();
      setIsRecording(false);
      return;
    }
    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      const rec = new MediaRecorder(stream);
      const chunks: BlobPart[] = [];

      rec.ondataavailable = e => chunks.push(e.data);
      rec.onstop = async () => {
        const blob = new Blob(chunks, { type: "audio/webm" });
        const form = new FormData();
        form.append("file", blob);
        await fetch(`${process.env.NEXT_PUBLIC_BACKEND_URL}/voice_stream`, {
          method: "POST",
          body: form,
        });
      };

      rec.start();
      setRecorder(rec);
      setIsRecording(true);
    } catch (err) {
      console.error("🎙️ voice error", err);
    }
  }

  useEffect(() => {
    const ws = new WebSocket(`${process.env.NEXT_PUBLIC_BACKEND_WS_URL}/spec_live_feedback`);
    ws.onmessage = ev => {
      try {
        const data = JSON.parse(ev.data);
        if (data.summary) setSummary(data.summary);
        if (data.coverage) setCoverage(data.coverage);
      } catch {}
    };
    return () => ws.close();
  }, []);

  return { isRecording, startStopRecording, summary, coverage };
}
