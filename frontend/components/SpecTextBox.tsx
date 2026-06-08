"use client";

import { useState } from "react";
import TextFileUpload from "@/components/TextFileUpload";
import VoiceSpecDraft from "@/components/VoiceSpecDraft";

type InsertMode = "append" | "replace";

type Props = {
  label: string;
  value: string;
  onChange: (value: string) => void;
  rows?: number;
  required?: boolean;
  voiceTitle: string;
  voiceLoopType: string;
  voiceTarget: string;
  uploadLabel: string;
  uploadHelper?: string;
};

function mergeText(current: string, incoming: string, mode: InsertMode) {
  if (mode === "append") return [current.trim(), incoming.trim()].filter(Boolean).join("\n\n");
  return incoming;
}

export default function SpecTextBox({
  label,
  value,
  onChange,
  rows = 6,
  required = false,
  voiceTitle,
  voiceLoopType,
  voiceTarget,
  uploadLabel,
  uploadHelper,
}: Props) {
  const [mode, setMode] = useState<InsertMode>("replace");

  return (
    <div>
      <label className="block text-sm text-slate-300">
        {label}
        {required ? " *" : ""}
      </label>
      <div className="mt-2 rounded-2xl border border-slate-800 bg-black/30 p-3">
        <textarea
          value={value}
          onChange={(event) => onChange(event.target.value)}
          rows={rows}
          className="w-full resize-y bg-transparent p-1 text-slate-100 outline-none"
        />
        <div className="mt-2 flex items-center justify-end gap-2">
          <select
            value={mode}
            onChange={(event) => setMode(event.target.value as InsertMode)}
            className="h-9 rounded-lg border border-slate-800 bg-black/40 px-2 text-xs text-slate-200"
            title="Choose whether voice/upload replaces or appends to the spec"
          >
            <option value="replace">Replace</option>
            <option value="append">Append</option>
          </select>
          <VoiceSpecDraft
            title={voiceTitle}
            loopType={voiceLoopType}
            target={voiceTarget}
            compact
            inline
            onApply={(draft) => onChange(mergeText(value, draft, mode))}
          />
          <TextFileUpload
            compact
            inline
            showMode={false}
            mode={mode}
            onModeChange={setMode}
            label={uploadLabel}
            helper={uploadHelper}
            onText={(text, _fileName, insertMode) => onChange(mergeText(value, text, insertMode))}
          />
        </div>
      </div>
    </div>
  );
}
