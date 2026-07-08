"use client";

import { useEffect, useMemo, useState } from "react";
import Editor from "@monaco-editor/react";
import { createClientComponentClient } from "@/lib/platformClient";
import { getStableUserId } from "@/utils/userId";

const supabase = createClientComponentClient();

type DesignIntentHandoff = {
  id?: string;
  title: string;
  refined_prompt: string;
  structured_intent: Record<string, string>;
  qa_pairs: Record<string, string>;
  full_intent: Record<string, unknown>;
};

type PlannerModalProps = {
  onClose: () => void;
  onBuildWorkflow?: (intent: DesignIntentHandoff) => void;
};

type LoopInterpretation = {
  digital?: string;
  embedded?: string;
  analog?: string;
  system?: string;
  validation?: string;
};

type SavedDesignIntent = Partial<DesignIntentHandoff> & {
  id?: string;
  title?: string;
  refined_prompt?: string;
  structured_intent?: LoopInterpretation;
  qa_pairs?: Record<string, string>;
  full_intent?: {
    refined_prompt?: string;
    [key: string]: unknown;
  };
};

export default function PlannerModal({ onClose, onBuildWorkflow }: PlannerModalProps) {
  const [activeStep, setActiveStep] = useState<"describe" | "clarify" | "review">("describe");
  const [userId, setUserId] = useState<string | null>(null);
  const [loadedIntent, setLoadedIntent] = useState<SavedDesignIntent | null>(null);
  const [titleHint, setTitleHint] = useState("My Design");
  const [ideaText, setIdeaText] = useState("");
  const [initialIdea, setInitialIdea] = useState("");
  const [roundNumber, setRoundNumber] = useState(1);
  const [clarifyQuestions, setClarifyQuestions] = useState<string[]>([]);
  const [answers, setAnswers] = useState<Record<string, string>>({});
  const [allQaPairs, setAllQaPairs] = useState<Record<string, string>>({});
  const [refinedPrompts, setRefinedPrompts] = useState<string[]>([]);
  const [loopInterpretation, setLoopInterpretation] = useState<LoopInterpretation>({});
  const [interpretationHistory, setInterpretationHistory] = useState<LoopInterpretation[]>([]);
  const [consolidatedSpec, setConsolidatedSpec] = useState("");
  const [loadingRound, setLoadingRound] = useState(false);
  const [saving, setSaving] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [jsonEditMode, setJsonEditMode] = useState(false);
  const [jsonContent, setJsonContent] = useState("");

  useEffect(() => {
    (async () => {
      const id = await getStableUserId(supabase);
      setUserId(id);
    })();
  }, []);

  useEffect(() => {
    const handleLoadIntent = (event: Event) => setLoadedIntent((event as CustomEvent<SavedDesignIntent>).detail);
    const handleJsonEdit = (event: Event) => {
      setJsonContent(JSON.stringify((event as CustomEvent<unknown>).detail, null, 2));
      setJsonEditMode(true);
    };

    window.addEventListener("loadDesignIntent", handleLoadIntent);
    window.addEventListener("openJsonEditorForDesignIntent", handleJsonEdit);
    return () => {
      window.removeEventListener("loadDesignIntent", handleLoadIntent);
      window.removeEventListener("openJsonEditorForDesignIntent", handleJsonEdit);
    };
  }, []);

  useEffect(() => {
    if (!loadedIntent) return;

    setTitleHint(loadedIntent.title || "My Design");
    setIdeaText(loadedIntent.refined_prompt || loadedIntent.full_intent?.refined_prompt || "");
    setConsolidatedSpec(loadedIntent.refined_prompt || loadedIntent.full_intent?.refined_prompt || "");
    setLoopInterpretation(loadedIntent.structured_intent || {});
    setInterpretationHistory(loadedIntent.structured_intent ? [loadedIntent.structured_intent] : []);

    const qa = loadedIntent.qa_pairs && typeof loadedIntent.qa_pairs === "object" ? loadedIntent.qa_pairs : {};
    setAnswers(qa);
    setAllQaPairs(qa);
    setClarifyQuestions(Object.keys(qa));
    setActiveStep("review");
  }, [loadedIntent]);

  const qaPairs = useMemo(() => ({ ...allQaPairs, ...answers }), [allQaPairs, answers]);

  function mergedInterpretation(): Required<Pick<LoopInterpretation, "digital" | "embedded" | "analog" | "system">> {
    const merged = { digital: "", embedded: "", analog: "", system: "" };
    for (const item of interpretationHistory) {
      merged.digital = merged.digital || item.digital || "";
      merged.embedded = merged.embedded || item.embedded || "";
      merged.analog = merged.analog || item.analog || "";
      merged.system = merged.system || item.system || item.validation || "";
    }
    return {
      digital: merged.digital || loopInterpretation.digital || "",
      embedded: merged.embedded || loopInterpretation.embedded || "",
      analog: merged.analog || loopInterpretation.analog || "",
      system: merged.system || loopInterpretation.system || loopInterpretation.validation || "",
    };
  }

  function cumulativePrompt() {
    const original = initialIdea || ideaText;
    const sections = [`### Original User Intent\n${original}`];
    refinedPrompts.forEach((prompt, index) => {
      if (prompt) sections.push(`### Refined Prompt Round ${index + 1}\n${prompt}`);
    });
    const qaText = Object.entries(qaPairs)
      .map(([question, answer]) => `Q: ${question}\nA: ${answer}`)
      .join("\n\n");
    if (qaText) sections.push(`### All Questions and Answers So Far\n${qaText}`);
    return sections.join("\n\n").trim();
  }

  function promptForNextRound() {
    const currentAnswers = Object.entries(answers)
      .filter(([, answer]) => answer.trim())
      .map(([question, answer]) => `${question}\n${answer}`)
      .join("\n\n");
    return [cumulativePrompt(), currentAnswers].filter(Boolean).join("\n\n").trim();
  }

  function buildConsolidatedDesignSpec() {
    const interpretation = mergedInterpretation();
    const answeredItems = Object.entries(qaPairs)
      .filter(([, answer]) => String(answer || "").trim())
      .map(([question, answer]) => `- ${question}\n  Answer: ${answer}`)
      .join("\n");
    const openItems = clarifyQuestions
      .filter((question) => !String(qaPairs[question] || "").trim())
      .map((question) => `- ${question}`)
      .join("\n");

    return [
      "# Consolidated Design Spec",
      "",
      "## Purpose",
      (ideaText || initialIdea || "Not specified.").trim(),
      "",
      "## Functional Intent",
      "Describe the required behavior, state transitions, data movement, and user-visible outcomes based on the captured requirements below.",
      "",
      "## Domain Interpretation",
      `- Digital: ${interpretation.digital || "Not specified"}`,
      `- Embedded: ${interpretation.embedded || "Not specified"}`,
      `- Analog: ${interpretation.analog || "Not specified"}`,
      `- System: ${interpretation.system || "Not specified"}`,
      "",
      "## Captured Requirements and Decisions",
      answeredItems || "- No clarifying answers captured yet.",
      "",
      "## Assumptions and Open Questions",
      openItems || "- No open questions currently captured.",
      "",
      "## Verification Intent",
      "Define checks, expected outputs, corner cases, and pass/fail criteria before running implementation workflows.",
      "",
      "## Recommended Next Step",
      "Use this saved design intent in System Planner to select agents and build an executable workflow.",
    ].join("\n");
  }

  function refreshConsolidatedSpec() {
    const spec = buildConsolidatedDesignSpec();
    setConsolidatedSpec(spec);
    setActiveStep("review");
    return spec;
  }

  async function continueQuestions() {
    const prompt = promptForNextRound();
    if (!prompt.trim()) return;

    setLoadingRound(true);
    setError(null);
    try {
      if (!initialIdea) setInitialIdea(ideaText);

      const response = await fetch("/api/clarify_intent_round", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          user_id: userId || "anonymous",
          round: roundNumber,
          prompt,
          previous_loop_interpretation: mergedInterpretation(),
        }),
      });
      const data = await response.json();
      if (data.status !== "ok") throw new Error(data.message || "Clarification failed.");

      const questions = data.questions || [];
      const suggested = data.suggested_answers || [];
      const mappedAnswers: Record<string, string> = {};
      questions.forEach((question: string, index: number) => {
        mappedAnswers[question] = suggested[index] || "";
      });

      setAllQaPairs((current) => ({ ...current, ...answers, ...mappedAnswers }));
      setAnswers(mappedAnswers);
      setClarifyQuestions(questions);
      setRefinedPrompts((current) => current.concat(data.refined_prompt || ""));
      setIdeaText(data.refined_prompt || ideaText);
      setLoopInterpretation(data.loop_interpretation || {});
      setInterpretationHistory((current) => current.concat(data.loop_interpretation || {}));
      setRoundNumber((current) => current + 1);
      setActiveStep("clarify");
    } catch (err) {
      setError(err instanceof Error ? err.message : "Could not connect to backend.");
    } finally {
      setLoadingRound(false);
    }
  }

  async function saveDesignIntent(continueToSystemPlanner: boolean) {
    const specText = consolidatedSpec.trim() ? consolidatedSpec : refreshConsolidatedSpec();
    const effectiveUserId = userId || (await getStableUserId(supabase));
    const title = window.prompt("Enter a name for this Design Intent:", titleHint) || titleHint || "Untitled Design Intent";
    const structuredIntent = mergedInterpretation();
    const payload = {
      user_id: effectiveUserId,
      title,
      refined_prompt: specText,
      implementation_strategy: [
        `Digital: ${structuredIntent.digital || ""}`,
        `Embedded: ${structuredIntent.embedded || ""}`,
        `Analog: ${structuredIntent.analog || ""}`,
        `System: ${structuredIntent.system || ""}`,
      ].join("\n"),
      structured_intent: structuredIntent,
      qa_pairs: qaPairs,
      full_intent: {
        refined_prompt: specText,
        raw_history: cumulativePrompt(),
        structured_intent: structuredIntent,
        qa_pairs: qaPairs,
        round: roundNumber - 1,
      },
      version: 1,
    };

    setSaving(true);
    setError(null);
    try {
      const response = await fetch("/api/save_design_intent_draft", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload),
      });
      const data = await response.json();
      if (data.status !== "ok") throw new Error(data.message || "Save failed.");

      const savedIntent = data.data || payload;
      window.dispatchEvent(new CustomEvent("refreshDesignIntents"));
      if (continueToSystemPlanner && onBuildWorkflow) {
        onBuildWorkflow(savedIntent);
      } else {
        onClose();
      }
    } catch (err) {
      setError(err instanceof Error ? err.message : "Could not save design intent.");
    } finally {
      setSaving(false);
    }
  }

  if (jsonEditMode) {
    return (
      <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/60 p-4">
        <div className="flex h-[90vh] w-[90vw] flex-col rounded-lg bg-slate-900 p-4 text-white">
          <h2 className="mb-3 text-lg font-bold">Edit Design Intent JSON</h2>
          <div className="min-h-0 flex-1 rounded border border-slate-700">
            <Editor
              height="100%"
              defaultLanguage="json"
              value={jsonContent}
              onChange={(value) => setJsonContent(value ?? "")}
              options={{ minimap: { enabled: false }, fontSize: 14, scrollBeyondLastLine: false, smoothScrolling: true }}
            />
          </div>
          <div className="mt-3 flex justify-end gap-3">
            <button className="rounded bg-slate-700 px-3 py-2 text-sm" onClick={() => setJsonEditMode(false)}>
              Cancel
            </button>
            <button
              className="rounded bg-emerald-700 px-3 py-2 text-sm font-semibold"
              onClick={async () => {
                try {
                  const parsed = JSON.parse(jsonContent);
                  const { error: updateError } = await supabase.from("design_intent_drafts").update(parsed).eq("id", parsed.id);
                  if (updateError) throw updateError;
                  window.dispatchEvent(new Event("refreshDesignIntents"));
                  setJsonEditMode(false);
                  onClose();
                } catch {
                  window.alert("JSON error. Fix before saving.");
                }
              }}
            >
              Save
            </button>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex h-[calc(100vh-2rem)] max-h-[920px] w-full max-w-5xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex shrink-0 items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-white">Design Intent Planner</h2>
            <p className="mt-1 text-sm text-slate-400">
              Capture an idea, clarify missing engineering details, and save a reusable design spec.
            </p>
          </div>
          <button onClick={onClose} className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900">
            Close
          </button>
        </div>

        <div className="shrink-0 border-b border-slate-800 px-5 py-3">
          <div className="flex flex-wrap gap-2">
            {[
              ["describe", "Describe"],
              ["clarify", "Clarify"],
              ["review", "Review"],
            ].map(([key, label]) => (
              <button
                key={key}
                type="button"
                onClick={() => {
                  if (key === "review" && !consolidatedSpec) refreshConsolidatedSpec();
                  else setActiveStep(key as "describe" | "clarify" | "review");
                }}
                className={`rounded-lg px-3 py-1.5 text-sm font-semibold ${
                  activeStep === key ? "bg-cyan-600 text-white" : "border border-slate-700 text-slate-300 hover:bg-slate-900"
                }`}
              >
                {label}
              </button>
            ))}
          </div>
        </div>

        <div className="min-h-0 flex-1 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {error ? <div className="mb-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">{error}</div> : null}

          {activeStep === "describe" ? (
            <section className="grid gap-5 lg:grid-cols-[1fr_320px]">
              <div>
                <label className="block text-lg font-bold text-slate-100">Design Your Idea</label>
                <textarea
                  className="mt-3 h-72 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-4 text-sm leading-6 text-slate-100 outline-none focus:border-cyan-600"
                  value={ideaText}
                  onChange={(event) => setIdeaText(event.target.value)}
                  placeholder="Example: Design a 4-bit counter with enable, active-low reset, terminal count output, and wrap-around behavior."
                />
              </div>
              <aside className="rounded-lg border border-slate-800 bg-black/30 p-4">
                <h3 className="text-sm font-bold text-white">Good inputs</h3>
                <ul className="mt-3 space-y-2 text-sm leading-5 text-slate-300">
                  <li>Design a 4-bit counter with enable, reset, and terminal count.</li>
                  <li>Create an SPI controller with APB interface and interrupt support.</li>
                  <li>Build a mixed-signal sensor readout with ADC, firmware driver, and validation plan.</li>
                </ul>
              </aside>
            </section>
          ) : null}

          {activeStep === "clarify" ? (
            <section className="grid gap-5 lg:grid-cols-[1fr_320px]">
              <div>
                <h3 className="text-lg font-bold text-slate-100">Clarifying Questions</h3>
                <p className="mt-1 text-sm text-slate-400">Edit the suggested answers so the saved design intent reflects your actual requirement.</p>
                <div className="mt-4 space-y-3">
                  {clarifyQuestions.length ? (
                    clarifyQuestions.map((question, index) => (
                      <div key={question} className="rounded-lg border border-slate-800 bg-black/30 p-3">
                        <p className="text-sm font-semibold text-slate-200">
                          {index + 1}. {question}
                        </p>
                        <input
                          className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-100 outline-none focus:border-cyan-600"
                          value={answers[question] || ""}
                          onChange={(event) => setAnswers({ ...answers, [question]: event.target.value })}
                          placeholder="Type or edit your answer"
                        />
                      </div>
                    ))
                  ) : (
                    <div className="rounded-lg border border-slate-800 bg-black/30 p-4 text-sm text-slate-400">
                      Click Continue Asking Questions to generate the first clarification set.
                    </div>
                  )}
                </div>
              </div>
              <aside className="rounded-lg border border-slate-800 bg-black/30 p-4">
                <h3 className="text-sm font-bold text-white">Domain Interpretation</h3>
                <dl className="mt-3 space-y-3 text-sm">
                  <div><dt className="text-slate-500">Digital</dt><dd className="text-slate-200">{mergedInterpretation().digital || "Not specified"}</dd></div>
                  <div><dt className="text-slate-500">Embedded</dt><dd className="text-slate-200">{mergedInterpretation().embedded || "Not specified"}</dd></div>
                  <div><dt className="text-slate-500">Analog</dt><dd className="text-slate-200">{mergedInterpretation().analog || "Not specified"}</dd></div>
                  <div><dt className="text-slate-500">System</dt><dd className="text-slate-200">{mergedInterpretation().system || "Not specified"}</dd></div>
                </dl>
              </aside>
            </section>
          ) : null}

          {activeStep === "review" ? (
            <section>
              <div className="flex flex-wrap items-center justify-between gap-3">
                <div>
                  <h3 className="text-lg font-bold text-slate-100">Review Consolidated Design Spec</h3>
                  <p className="mt-1 text-sm text-slate-400">Edit this spec before saving it to the Design Intent Library or building a workflow.</p>
                </div>
                <button
                  type="button"
                  onClick={refreshConsolidatedSpec}
                  className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900"
                >
                  Regenerate Spec
                </button>
              </div>
              <textarea
                className="mt-4 h-[52vh] w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-4 font-mono text-xs leading-5 text-slate-100 outline-none focus:border-cyan-600"
                value={consolidatedSpec}
                onChange={(event) => setConsolidatedSpec(event.target.value)}
              />
            </section>
          ) : null}
        </div>

        <div className="flex shrink-0 flex-wrap justify-between gap-3 border-t border-slate-800 bg-slate-950/95 p-4">
          <button
            onClick={continueQuestions}
            disabled={loadingRound || !ideaText.trim()}
            className="rounded-lg bg-emerald-700 px-4 py-2 text-sm font-bold text-white hover:bg-emerald-600 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
          >
            {loadingRound ? "Thinking..." : "Continue Asking Questions"}
          </button>
          <div className="flex flex-wrap gap-2">
            <button
              onClick={refreshConsolidatedSpec}
              disabled={!ideaText.trim() && !Object.keys(qaPairs).length}
              className="rounded-lg border border-cyan-700 px-4 py-2 text-sm font-semibold text-cyan-100 hover:bg-cyan-950/40 disabled:cursor-not-allowed disabled:border-slate-800 disabled:text-slate-500"
            >
              Generate Consolidated Spec
            </button>
            <button
              onClick={() => saveDesignIntent(false)}
              disabled={saving || activeStep !== "review" || !consolidatedSpec.trim()}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
            >
              {saving ? "Saving..." : "Save Design Intent"}
            </button>
            <button
              onClick={() => saveDesignIntent(true)}
              disabled={saving || activeStep !== "review" || !consolidatedSpec.trim()}
              className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
            >
              Save & Build Workflow
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}
