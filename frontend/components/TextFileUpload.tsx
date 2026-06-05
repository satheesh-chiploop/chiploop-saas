"use client";

import { useState } from "react";

type Props = {
  label: string;
  helper?: string;
  onText: (text: string, fileName: string, mode: "append" | "replace") => void;
  accept?: string;
};

const DEFAULT_ACCEPT = ".txt,.md,.json,.yaml,.yml,.sv,.v,.sdc";
const MAX_BYTES = 2 * 1024 * 1024;

export default function TextFileUpload({ label, helper, onText, accept = DEFAULT_ACCEPT }: Props) {
  const [mode, setMode] = useState<"append" | "replace">("replace");
  const [fileName, setFileName] = useState("");
  const [error, setError] = useState("");

  async function handleFile(file: File | undefined) {
    setError("");
    if (!file) return;
    if (file.size > MAX_BYTES) {
      setError("File is too large. Upload a text spec under 2 MB.");
      return;
    }
    try {
      const text = await file.text();
      setFileName(file.name);
      onText(text, file.name, mode);
    } catch {
      setError("Could not read this file as text.");
    }
  }

  return (
    <div className="rounded-xl border border-slate-800 bg-black/25 p-3">
      <div className="flex flex-col gap-2 sm:flex-row sm:items-center sm:justify-between">
        <div>
          <div className="text-sm font-semibold text-slate-200">{label}</div>
          {helper ? <div className="mt-1 text-xs text-slate-500">{helper}</div> : null}
        </div>
        <select
          value={mode}
          onChange={(e) => setMode(e.target.value as "append" | "replace")}
          className="rounded-lg border border-slate-800 bg-black/40 px-2 py-1 text-xs text-slate-200"
        >
          <option value="replace">Replace text</option>
          <option value="append">Append to text</option>
        </select>
      </div>
      <input
        type="file"
        accept={accept}
        onChange={(e) => void handleFile(e.target.files?.[0])}
        className="mt-3 block w-full text-xs text-slate-400 file:mr-3 file:rounded-lg file:border-0 file:bg-slate-800 file:px-3 file:py-2 file:text-xs file:font-semibold file:text-slate-100 hover:file:bg-slate-700"
      />
      {fileName ? <div className="mt-2 text-xs text-slate-500">Loaded {fileName}</div> : null}
      {error ? <div className="mt-2 text-xs text-red-300">{error}</div> : null}
    </div>
  );
}
