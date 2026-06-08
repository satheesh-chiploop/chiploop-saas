"use client";

import { useState } from "react";
import { FiUpload } from "react-icons/fi";

type Props = {
  label: string;
  helper?: string;
  onText: (text: string, fileName: string, mode: "append" | "replace") => void;
  accept?: string;
  compact?: boolean;
};

const DEFAULT_ACCEPT = ".txt,.md,.json,.yaml,.yml,.sv,.v,.sdc";
const MAX_BYTES = 2 * 1024 * 1024;

export default function TextFileUpload({ label, helper, onText, accept = DEFAULT_ACCEPT, compact = false }: Props) {
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
    <div className={`rounded-xl border border-slate-800 bg-black/25 ${compact ? "p-2" : "p-3"}`}>
      <div className="flex flex-col gap-2 sm:flex-row sm:items-center sm:justify-between">
        <div className={compact ? "sr-only" : ""}>
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
      <label
        title={label}
        className={
          compact
            ? "mt-2 inline-flex cursor-pointer items-center rounded-lg border border-slate-700 bg-slate-900 px-3 py-2 text-slate-100 transition hover:bg-slate-800"
            : "mt-3 inline-flex cursor-pointer items-center gap-2 rounded-lg border border-slate-700 bg-slate-900 px-3 py-2 text-xs font-semibold text-slate-100 transition hover:bg-slate-800"
        }
      >
        <FiUpload aria-hidden="true" />
        {compact ? <span className="sr-only">{label}</span> : <span>Upload</span>}
        <input
          type="file"
          accept={accept}
          onChange={(e) => void handleFile(e.target.files?.[0])}
          className="sr-only"
        />
      </label>
      {fileName ? <div className="mt-2 text-xs text-slate-500">Loaded {fileName}</div> : null}
      {error ? <div className="mt-2 text-xs text-red-300">{error}</div> : null}
    </div>
  );
}
