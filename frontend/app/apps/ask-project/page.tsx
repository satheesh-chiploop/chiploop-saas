"use client";

import { FormEvent, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { apiPost } from "@/lib/apiClient";
import GitHubImportPanel from "@/components/GitHubImportPanel";
import TopNav from "@/components/TopNav";

type ProjectFile = {
  path: string;
  content: string;
};

type AskProjectResponse = {
  status: string;
  project_name: string;
  question: string;
  answer: string;
  sources?: Array<{ path: string; chars?: number }>;
  source_count?: number;
};

const suggestions = [
  "Summarize this project and the most important files.",
  "What risks or missing pieces should I fix first?",
  "Suggest the next ChipLoop workflow or app to run.",
  "Review this project for verification and validation gaps.",
  "Explain the architecture and key interfaces.",
];

const textExtensions = [
  ".v",
  ".sv",
  ".svh",
  ".vhd",
  ".vhdl",
  ".c",
  ".h",
  ".cpp",
  ".hpp",
  ".rs",
  ".py",
  ".js",
  ".ts",
  ".tsx",
  ".json",
  ".yaml",
  ".yml",
  ".toml",
  ".md",
  ".txt",
  ".log",
  ".rpt",
  ".sdc",
  ".upf",
  ".tcl",
  ".sh",
  ".csv",
];

function isLikelyTextFile(name: string): boolean {
  const lowered = name.toLowerCase();
  return textExtensions.some((extension) => lowered.endsWith(extension));
}

function trimContent(content: string): string {
  return content.length > 12000 ? `${content.slice(0, 12000)}\n[TRUNCATED IN BROWSER]` : content;
}

export default function AskProjectPage() {
  const router = useRouter();
  const [projectName, setProjectName] = useState("Uploaded project");
  const [files, setFiles] = useState<ProjectFile[]>([]);
  const [manualPath, setManualPath] = useState("notes.md");
  const [manualContent, setManualContent] = useState("");
  const [question, setQuestion] = useState("");
  const [history, setHistory] = useState<AskProjectResponse[]>([]);
  const [loading, setLoading] = useState(false);
  const [fileLoading, setFileLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const totalChars = useMemo(() => files.reduce((sum, file) => sum + file.content.length, 0), [files]);

  async function addSelectedFiles(selectedFiles: FileList | null) {
    if (!selectedFiles?.length) return;
    setFileLoading(true);
    setError(null);
    try {
      const loaded: ProjectFile[] = [];
      for (const file of Array.from(selectedFiles).slice(0, 40)) {
        if (!isLikelyTextFile(file.name)) continue;
        const text = await file.text();
        loaded.push({ path: file.webkitRelativePath || file.name, content: trimContent(text) });
      }
      if (!loaded.length) {
        setError("No supported text files found. Try RTL, code, specs, logs, reports, markdown, JSON, YAML, SDC, UPF, or scripts.");
        return;
      }
      setFiles((current) => {
        const byPath = new Map(current.map((file) => [file.path, file]));
        loaded.forEach((file) => byPath.set(file.path, file));
        return Array.from(byPath.values()).slice(0, 40);
      });
    } catch (err) {
      setError(err instanceof Error ? err.message : "Could not read files.");
    } finally {
      setFileLoading(false);
    }
  }

  function addManualFile() {
    const path = manualPath.trim() || "notes.md";
    const content = manualContent.trim();
    if (!content) return;
    setFiles((current) => {
      const byPath = new Map(current.map((file) => [file.path, file]));
      byPath.set(path, { path, content: trimContent(content) });
      return Array.from(byPath.values()).slice(0, 40);
    });
    setManualContent("");
  }

  function removeFile(path: string) {
    setFiles((current) => current.filter((file) => file.path !== path));
  }

  function importGitHubFiles(importedFiles: Array<{ path: string; content: string }>, source: { owner: string; repo: string; ref: string }) {
    if (!importedFiles.length) return;
    setProjectName((current) => current === "Uploaded project" ? `${source.owner}/${source.repo}` : current);
    setFiles((current) => {
      const byPath = new Map(current.map((file) => [file.path, file]));
      importedFiles.forEach((file) => {
        byPath.set(`github:${source.owner}/${source.repo}@${source.ref}/${file.path}`, {
          path: `github:${source.owner}/${source.repo}@${source.ref}/${file.path}`,
          content: trimContent(file.content || ""),
        });
      });
      return Array.from(byPath.values()).slice(0, 40);
    });
  }

  async function ask(questionOverride?: string) {
    const text = (questionOverride || question).trim();
    if (!text || loading) return;
    if (!files.length) {
      setError("Add at least one project file before asking.");
      return;
    }
    setLoading(true);
    setError(null);
    try {
      const response = await apiPost<AskProjectResponse>("/project/ask", {
        project_name: projectName,
        question: text,
        files,
      });
      setHistory((current) => [response, ...current].slice(0, 10));
      setQuestion("");
    } catch (err) {
      setError(err instanceof Error ? err.message : "Ask this project failed.");
    } finally {
      setLoading(false);
    }
  }

  function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    ask();
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="apps" showMarketplace />
      <div className="mx-auto max-w-7xl px-6 py-8">
        <div className="flex flex-wrap items-center justify-between gap-3">
          <button onClick={() => router.push("/apps")} className="rounded-xl border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900">
            Back to Apps
          </button>
          <button onClick={() => router.push("/workflow")} className="rounded-xl border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900">
            Open Studio
          </button>
        </div>

        <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/70 p-6">
          <div className="grid grid-cols-1 gap-6 lg:grid-cols-[0.9fr_1.1fr]">
            <div>
              <div className="text-sm font-bold uppercase tracking-wide text-cyan-300">Project Intake</div>
              <h1 className="mt-2 text-3xl font-extrabold text-white">Ask this Project</h1>
              <p className="mt-3 leading-7 text-slate-300">
                Chat with uploaded files, codebases, specs, reports, logs, scripts, and docs. Ask for summaries, risks, suggestions, and the next ChipLoop workflow to run.
              </p>
              <div className="mt-5 grid grid-cols-1 gap-3 text-sm text-slate-300 sm:grid-cols-2">
                <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-4">
                  <div className="font-bold text-slate-100">Ask anything</div>
                  <p className="mt-2 text-slate-400">Architecture, missing files, review gaps, failure reports, handoff readiness, or workflow suggestions.</p>
                </div>
                <div className="rounded-xl border border-slate-800 bg-slate-950/60 p-4">
                  <div className="font-bold text-slate-100">Upload or import</div>
                  <p className="mt-2 text-slate-400">Use local files, pasted content, or selected GitHub repository files as project context.</p>
                </div>
              </div>
            </div>

            <div className="rounded-xl border border-slate-800 bg-slate-950/70 p-5">
              <label className="block">
                <span className="text-sm font-semibold text-slate-300">Project name</span>
                <input
                  value={projectName}
                  onChange={(event) => setProjectName(event.target.value)}
                  className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 px-4 py-3 text-slate-100 outline-none focus:border-cyan-500"
                />
              </label>
              <div className="mt-4 grid grid-cols-1 gap-3 sm:grid-cols-2">
                <label className="block rounded-lg border border-dashed border-slate-700 p-4 text-center hover:border-cyan-500">
                  <span className="text-sm font-bold text-cyan-200">Upload files</span>
                  <span className="mt-1 block text-xs text-slate-500">Select multiple text files</span>
                  <input
                    type="file"
                    multiple
                    className="hidden"
                    onChange={(event) => addSelectedFiles(event.target.files)}
                  />
                </label>
                <label className="block rounded-lg border border-dashed border-slate-700 p-4 text-center hover:border-cyan-500">
                  <span className="text-sm font-bold text-cyan-200">Upload folder</span>
                  <span className="mt-1 block text-xs text-slate-500">Chrome/Edge directory picker</span>
                  <input
                    type="file"
                    multiple
                    {...({ webkitdirectory: "" } as Record<string, string>)}
                    className="hidden"
                    onChange={(event) => addSelectedFiles(event.target.files)}
                  />
                </label>
              </div>
              <div className="mt-3 text-xs text-slate-500">
                {fileLoading ? "Reading files..." : `${files.length} file(s), ${totalChars.toLocaleString()} characters loaded`}
              </div>
            </div>
          </div>
        </section>

        <div className="mt-6 grid grid-cols-1 gap-6 lg:grid-cols-[0.9fr_1.1fr]">
          <section className="rounded-2xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-xl font-extrabold text-white">Project files</h2>
            <div className="mt-4">
              <GitHubImportPanel
                compact
                onImport={(_text, importedFiles, source) => importGitHubFiles(importedFiles, source)}
              />
            </div>
            <div className="mt-4 space-y-3">
              <div className="grid grid-cols-1 gap-3 sm:grid-cols-[0.45fr_1fr]">
                <input
                  value={manualPath}
                  onChange={(event) => setManualPath(event.target.value)}
                  className="rounded-lg border border-slate-700 bg-slate-950 px-4 py-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
                  placeholder="file path"
                />
                <button
                  type="button"
                  onClick={addManualFile}
                  disabled={!manualContent.trim()}
                  className="rounded-lg bg-cyan-500 px-4 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400 disabled:cursor-not-allowed disabled:bg-slate-700 disabled:text-slate-400"
                >
                  Add pasted file
                </button>
              </div>
              <textarea
                value={manualContent}
                onChange={(event) => setManualContent(event.target.value)}
                className="min-h-36 w-full rounded-lg border border-slate-700 bg-slate-950 px-4 py-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
                placeholder="Paste code, spec, log, report, constraints, README, or notes..."
              />
            </div>

            <div className="mt-5 max-h-96 space-y-2 overflow-y-auto pr-1">
              {files.length ? files.map((file) => (
                <div key={file.path} className="flex items-start justify-between gap-3 rounded-lg border border-slate-800 bg-slate-950/70 p-3">
                  <div className="min-w-0">
                    <div className="truncate text-sm font-semibold text-slate-100">{file.path}</div>
                    <div className="mt-1 text-xs text-slate-500">{file.content.length.toLocaleString()} chars</div>
                  </div>
                  <button onClick={() => removeFile(file.path)} className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:border-red-400 hover:text-red-200">
                    Remove
                  </button>
                </div>
              )) : (
                <div className="rounded-lg border border-slate-800 bg-slate-950/70 p-4 text-sm text-slate-400">
                  Add files to start a project conversation.
                </div>
              )}
            </div>
          </section>

          <section className="rounded-2xl border border-slate-800 bg-slate-900/70 p-6">
            <h2 className="text-xl font-extrabold text-white">Ask questions</h2>
            <div className="mt-3 flex flex-wrap gap-2">
              {suggestions.map((suggestion) => (
                <button
                  key={suggestion}
                  type="button"
                  disabled={loading || !files.length}
                  onClick={() => ask(suggestion)}
                  className="rounded border border-cyan-800 px-3 py-1 text-xs text-cyan-100 hover:bg-cyan-900/40 disabled:cursor-not-allowed disabled:opacity-50"
                >
                  {suggestion}
                </button>
              ))}
            </div>

            <form onSubmit={submit} className="mt-4 space-y-3">
              <textarea
                value={question}
                onChange={(event) => setQuestion(event.target.value)}
                className="min-h-28 w-full rounded-lg border border-slate-700 bg-slate-950 px-4 py-3 text-sm text-slate-100 outline-none focus:border-cyan-500"
                placeholder="Ask for a summary, project risks, code review, missing files, next workflow, or implementation suggestions..."
              />
              <button
                type="submit"
                disabled={loading || question.trim().length < 3 || !files.length}
                className="rounded-lg bg-cyan-500 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400 disabled:cursor-not-allowed disabled:bg-slate-700 disabled:text-slate-400"
              >
                {loading ? "Inspecting project..." : "Ask this project"}
              </button>
            </form>

            {error ? <div className="mt-4 rounded-lg border border-red-800 bg-red-950/40 p-3 text-sm text-red-200">{error}</div> : null}

            <div className="mt-5 space-y-4">
              {history.map((item, index) => (
                <article key={`${item.question}-${index}`} className="rounded-xl border border-slate-800 bg-slate-950/70 p-4">
                  <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">Question</div>
                  <div className="mt-1 text-slate-100">{item.question}</div>
                  <div className="mt-4 text-xs font-semibold uppercase tracking-wide text-cyan-300">Answer</div>
                  <div className="mt-2 whitespace-pre-wrap leading-6 text-slate-200">{item.answer}</div>
                  {item.sources?.length ? (
                    <div className="mt-4">
                      <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">Sources</div>
                      <div className="mt-2 flex flex-wrap gap-2">
                        {item.sources.slice(0, 12).map((source) => (
                          <span key={source.path} className="rounded bg-slate-800 px-2 py-1 text-xs text-slate-300">
                            {source.path}
                          </span>
                        ))}
                      </div>
                    </div>
                  ) : null}
                </article>
              ))}
            </div>
          </section>
        </div>
      </div>
    </main>
  );
}
