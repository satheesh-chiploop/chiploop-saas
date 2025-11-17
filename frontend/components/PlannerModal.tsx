"use client";
import { useState, useEffect } from "react";
import { useVoiceAnalyzer } from "@/hooks/useVoiceAnalyzer";
import { getStableUserId } from "@/utils/userId";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
const supabase = createClientComponentClient();
import Editor from "@monaco-editor/react";

export default function PlannerModal({ onClose }) {
    const [goal, setGoal] = useState("");
    const [plan, setPlan] = useState<any | null>(null);
    const [coverage, setCoverage] = useState<any | null>(null);
    const [liveCoverage, setLiveCoverage] = useState(0);
    const [clarifications, setClarifications] = useState<string[]>([]);
    const [analyzing, setAnalyzing] = useState(false);
    const [loading, setLoading] = useState(false);
    const [autoLoading, setAutoLoading] = useState(false);

    const [isRecording, setIsRecording] = useState(false);
    const [mediaRecorder, setMediaRecorder] = useState<MediaRecorder | null>(null);

    const [summary, setSummary] = useState<any>(null);
    const [voiceMode, setVoiceMode] = useState(false);

    const [designIntents, setDesignIntents] = useState<any[]>([]);
    const [loadedIntent, setLoadedIntent] = useState<any | null>(null);


    const [jsonEditMode, setJsonEditMode] = useState(false);
    const [jsonContent, setJsonContent] = useState("");

    useEffect(() => {
      const handler = (e) => {
          setLoadedIntent(e.detail);
      };
      window.addEventListener("loadDesignIntent", handler);
      return () => window.removeEventListener("loadDesignIntent", handler);
    }, []);

    useEffect(() => {
      if (!loadedIntent) return;
    
      console.log("📥 Hydrating planner with loaded intent:", loadedIntent);
    
      if (loadedIntent.refined_prompt) {
        setRefinedPrompt(loadedIntent.refined_prompt);
      }
      if (loadedIntent.structured_intent) {
        setLoopInterpretation(loadedIntent.structured_intent);
      }
      if (loadedIntent.qa_pairs) {
        setAnswers(loadedIntent.qa_pairs);
        setClarifyQuestions(Object.keys(loadedIntent.qa_pairs));
      }
    }, [loadedIntent]);

    useEffect(() => {
      const handleOpenJsonEditor = (e: any) => {
        console.log("🟢 PlannerModal RECEIVED event:", e.detail);
        const intent = e.detail;
        setJsonContent(JSON.stringify(intent, null, 2)); // pretty JSON
        setJsonEditMode(true);
      };
    
      window.addEventListener("openJsonEditorForDesignIntent", handleOpenJsonEditor);
    
      return () => {
        window.removeEventListener("openJsonEditorForDesignIntent", handleOpenJsonEditor);
      };
    }, []);
    

    const mergeAnswersIntoPrompt = () => {
      let merged = refinedPrompt;
      console.log("🧩 mergeAnswersIntoPrompt – clarifyQuestions:", clarifyQuestions);
      console.log("🧩 mergeAnswersIntoPrompt – answers:", answers);
      clarifyQuestions.forEach((q) => {
        const ans = answers[q];
        if (ans) {
          merged += `\n\n${q}\n${ans}`;
        }
      });
      return merged;
    };

  
    

    // When user clicks an item, hydrate the planner with it
    const handleLoadIntentIntoPlanner = (intent: any) => {
      console.log("📥 Loading design intent into planner:", intent?.id);
      if (intent?.refined_prompt) {
        setRefinedPrompt(intent.refined_prompt);
      }
      if (intent?.structured_intent) {
        setLoopInterpretation(intent.structured_intent);
      }

      // Optional: future-proof for qa_pairs if you add that column later
      const maybeQa = (intent as any).qa_pairs;
      if (maybeQa && typeof maybeQa === "object") {
        setClarifyQuestions(Object.keys(maybeQa));
        setAnswers(maybeQa);
      }
    };

    // -----------------------------
    // 🧩 Design Intent Planner state
    // -----------------------------
    const [isDesignIntentMode, setIsDesignIntentMode] = useState(true); // temporary toggle
    const [roundNumber, setRoundNumber] = useState(1);
    const [clarifyQuestions, setClarifyQuestions] = useState<string[]>([]);
    const [suggestedAnswers, setSuggestedAnswers] = useState<Record<string, string>>({});
    const [refinedPrompt, setRefinedPrompt] = useState("");
    const [loopInterpretation, setLoopInterpretation] = useState<{
        digital?: string;
        embedded?: string;
        analog?: string;
        system?: string;
    } | null>(null);
    const [isLoadingRound, setIsLoadingRound] = useState(false);
    const [answers, setAnswers] = useState<Record<string, string>>({});

    const [userId, setUserId] = useState(null);
    const [allRoundsQA, setAllRoundsQA] = useState({});
    const [allRefinedPrompts, setAllRefinedPrompts] = useState([]);
    const [allInterpretations, setAllInterpretations] = useState([]);
    const [initialUserIntent, setInitialUserIntent] = useState("");

    useEffect(() => {
      (async () => {
        const id = await getStableUserId(supabase);
        setUserId(id);
      })();
    }, []);

 
    async function startStopRecording() {
        if (isRecording && mediaRecorder) {
          mediaRecorder.stop();
          setIsRecording(false);
          return;
        }
      
        try {
          const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
          const rec = new MediaRecorder(stream);
          const chunks: BlobPart[] = [];
      
          rec.ondataavailable = (e) => chunks.push(e.data);
          rec.onstop = async () => {
            const blob = new Blob(chunks, { type: "audio/webm" });
            const formData = new FormData();
            formData.append("file", blob);
      
            // Send audio to backend
            await fetch("/voice_stream", {
              method: "POST",
              body: formData,
            });
            setVoiceMode(true);
          };
      
          rec.start();
          setMediaRecorder(rec);
          setIsRecording(true);
        } catch (err) {
          console.error("🎙️ Voice recording failed:", err);
        }
    }
    function toggleVoiceMode() {
        startStopRecording();
    }

    const handlePlan = async () => {
        setLoading(true);
        setPlan(null);
        try {
          
            const res = await fetch("/api/plan_workflow", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({ 
                    prompt:goal,
                    structured_spec_final: coverage?.structured_spec_final || summary?.structured_spec_final,
                }),
            });
            const data = await res.json();

            // ✅ capture the proper preplan structure only
          
            setPlan(data);

            console.log("🧠 Stored Preplan:", data);
            alert("✅ Plan generated successfully! Check for missing agents below.");
        } catch (err) {
            alert("⚠️ Failed to generate workflow plan");
        } finally {
            setLoading(false);
        }
    };
    const handleAutoCompose = async () => {
        setAutoLoading(true);
        try {
          const res = await fetch("/api/auto_compose_workflow", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({
              goal,
              preplan: plan || null,
              structured_spec_final: coverage?.structured_spec_final || summary?.structured_spec_final,
            }),
          });
      
          const data = await res.json();
      
          if (data.status === "ok" || data.nodes) {
            // ✅ Update plan state for canvas rendering
            setPlan({
              summary: data.summary,
              nodes: data.nodes,
              edges: data.edges,
            });
      
            // ✅ Save workflow to DB
            const workflowName = prompt(
              "💾 Enter a name to save this workflow:",
              `AI_Composed_${new Date().toISOString().slice(0, 10)}`
            );
            const loopType = prompt(
              "🔁 Enter loop type (digital / analog / embedded / system):",
              "digital"
            );
      
                        
            
      
            alert(`✅ Auto-composed workflow:\n${data.summary}`);
            alert("✅ Auto-Compose complete!\n🔍 Missing Agents → Auto-created if required.");
            window.dispatchEvent(new Event("workflow-saved"));
          } else {
            alert(`⚠️ ${data.message || "Auto-compose failed."}`);
          }
        } catch (err) {
          console.error(err);
          alert("❌ Could not connect to backend");
        } finally {
          setAutoLoading(false);
        }
    };
      
    

    const handleVoiceInput = async (file) => {
        const formData = new FormData();
        formData.append("file", file);
      
        const res = await fetch("/api/voice_to_spec", { method: "POST", body: formData });
        const data = await res.json();
        setSummary(data.summary || "");
        setCoverage(data.coverage || 0);
        setVoiceMode(true);
      };

    const handleAnalyzeSpec = async () => {
        setAnalyzing(true);
        try {
          // 🧩 Unified payload — use voice summary if voiceMode is active
          const payload = voiceMode
            ? { voice_summary: summary, user_id: "anonymous" }
            : { goal, user_id: "anonymous" };
      
          const res = await fetch("/api/analyze_spec", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify(payload),
          });
      
          const data = await res.json();
          if (data.status === "ok") {
            setCoverage(data.coverage);
            setClarifications(data.coverage.questions || []);
            alert("✅ Spec analyzed successfully!");
          } else {
            console.warn("⚠️ Spec analysis failed:", data.message);
            alert("⚠️ Spec analysis failed.");
          }
        } catch (err) {
          console.error("❌ Analyzer error:", err);
          alert("❌ Could not connect to backend.");
        } finally {
          setAnalyzing(false);
        }
      };
    // -----------------------------
    // 🧩 Phase 1 placeholder handlers
    // -----------------------------
    const handleContinueRound = async () => {
      try {

        const nextPrompt = mergeAnswersIntoPrompt();

        // Capture original refinedPrompt only during ROUND 1
        if (roundNumber === 1 && initialUserIntent === "") {
          setInitialUserIntent(refinedPrompt);
        }

        const res = await fetch("/api/clarify_intent_round", {
          method: "POST",
          headers: {
            "Content-Type": "application/json"
          },
          body: JSON.stringify({
            user_id: userId,
            round: roundNumber,
            prompt:  buildCumulativePrompt(),
            previous_loop_interpretation: buildMergedLoopInterpretation(),
          })
        });
    
        const data = await res.json();
    
        if (data.status === "ok") {
          // update state from backend response
          setClarifyQuestions(data.questions || []);
          
          // suggested_answers is an array → convert to { question: answer }
          // FIX: map suggested answers into answers

          const qs = data.questions || [];
          const sas = data.suggested_answers || [];   // ARRAY from backend

          console.log("🟢 Questions:", qs);
          console.log("🟢 Suggested answers array:", sas);

          const mappedAnswers: Record<string, string> = {};

          qs.forEach((q, idx) => {
            mappedAnswers[q] = sas[idx] || "";
          });

          console.log("🟢 Final mappedAnswers:", mappedAnswers);
          setSuggestedAnswers(prev => ({ ...prev, ...mappedAnswers }));
          setAnswers(mappedAnswers);
          

          setAllRoundsQA(prev => ({
           ...prev,
           ...mappedAnswers,
          }));



          
         
          setRefinedPrompt(data.refined_prompt || refinedPrompt);

          setAllRefinedPrompts(prev => [...prev, data.refined_prompt]);

          setLoopInterpretation(data.loop_interpretation || loopInterpretation);
          setAllInterpretations(prev => [...prev, data.loop_interpretation]);
          // Next round
          setRoundNumber(prev => prev + 1);
        } else {
          console.error("Backend error:", data.message);
        }
      } catch (err) {
        console.error("Network error:", err);
      }
    };

    const buildCumulativePrompt = () => {
      let final = "### Original User Intent\n" + initialUserIntent + "\n\n";
    
      let i = 1;
      for (const prompt of allRefinedPrompts) {
        final += `### Refined Prompt Round ${i}\n${prompt}\n\n`;
        i++;
      }
    
      final += "### All Questions and Answers So Far\n";
      for (const [q, a] of Object.entries(allRoundsQA)) {
        final += `Q: ${q}\nA: ${a}\n\n`;
      }
    
      return final.trim();
    };

    const buildMergedLoopInterpretation = () => {
      const merged = { digital: "", embedded: "", analog: "", system: "" };
    
      allInterpretations.forEach(int => {
        if (!int) return;
        merged.digital = merged.digital || int.digital || "";
        merged.embedded = merged.embedded || int.embedded || "";
        merged.analog = merged.analog || int.analog || "";
        merged.system = merged.system || int.system || "";
      });
    
      return merged;
    };
    
    const handleFinalizeDesignIntent = async () => {
      try {

        const effectiveUserId = userId || (await getStableUserId(supabase));
        if (!userId && effectiveUserId) {
          setUserId(effectiveUserId);
        }
        // If we loaded an existing intent, use its title as default
        const existingTitle = loadedIntent?.title || "My Design";
        let title = prompt("Enter a name for this Design Intent:", existingTitle);
        if (!title) title = existingTitle || "Untitled Design Intent";


        const payload = {
          user_id: effectiveUserId,
          title,
          refined_prompt: buildCumulativePrompt(),
          implementation_strategy: `
            Digital: ${buildMergedLoopInterpretation().digital || ""}
            Embedded: ${buildMergedLoopInterpretation().embedded || ""}
            Analog: ${buildMergedLoopInterpretation().analog || ""}
            System: ${buildMergedLoopInterpretation().system || ""}
          `.trim(),
          structured_intent: buildMergedLoopInterpretation(),
          qa_pairs: allRoundsQA,                       // NEW
          full_intent: {                           // NEW (optional)
            refined_prompt:buildCumulativePrompt(),
            structured_intent: buildMergedLoopInterpretation(),
            qa_pairs: allRoundsQA,
            round: roundNumber-1
          },
          version: 1,
        };
        
        const response = await fetch("/api/save_design_intent_draft", {
          method: "POST",
          headers: {
            "Content-Type": "application/json",
          },
          body: JSON.stringify(payload),
        });
    
        const data = await response.json();
        console.log("Save design intent:", data);
    
        if (data.status === "ok") {
          alert("Design Intent Draft saved successfully!");
          onClose(); // Close modal after save
        } else {
          console.error("Save failed:", data.message);
        }
        window.dispatchEvent(new CustomEvent("refreshDesignIntents"));

      } catch (err) {
        console.error("Save intent network error:", err);
      }
    };
    
    
    useEffect(() => {
        const ws = new WebSocket("wss://209.38.74.151/spec_live_feedback");
      
        ws.onmessage = (event) => {
          try {
            const data = JSON.parse(event.data);
            if (data.summary) setSummary(data.summary);
            if (data.coverage) setLiveCoverage(data.coverage);
          } catch (err) {
            console.error("⚠️ Error parsing WebSocket data", err);
          }
        };
      
        return () => ws.close();
    }, []);

    if (jsonEditMode) {
      return (
        <div className="fixed inset-0 bg-black/60 flex items-center justify-center z-50">
          <div className="bg-slate-900 p-4 rounded w-[90%] h-[90%] flex flex-col">
            <h2 className="text-lg font-bold mb-3">Edit Design Intent (JSON)</h2>
    
            <div className="flex-1 border border-slate-700 rounded">
              <Editor
                height="100%"
                defaultLanguage="json"
                value={jsonContent}
                onChange={(value) => setJsonContent(value ?? "")}
                options={{
                  minimap: { enabled: false },
                  fontSize: 14,
                  scrollBeyondLastLine: false,
                  smoothScrolling: true,
                }}
              />
            </div>
    
            <div className="mt-3 flex justify-end gap-3">
              <button
                className="px-3 py-1 bg-slate-600 rounded"
                onClick={() => {
                  setJsonEditMode(false);
                  onClose();
                }}
              >
                Cancel
              </button>
    
              <button
                className="px-3 py-1 bg-green-600 rounded"
                onClick={async () => {
                  try {
                    const parsed = JSON.parse(jsonContent);
    
                    const { error } = await supabase
                      .from("design_intent_drafts")
                      .update(parsed)
                      .eq("id", parsed.id);
    
                    if (error) {
                      alert("Save failed: " + error.message);
                      return;
                    }
    
                    window.dispatchEvent(new Event("refreshDesignIntents"));
                    setJsonEditMode(false);
                    onClose();

                  } catch (err) {
                    alert("JSON Error — fix before saving.");
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
        <div className="fixed inset-0 bg-black/70 flex items-center justify-center z-50">
            <div className="bg-slate-800 relative rounded-xl p-6 w-[600px] shadow-xl text-white">
                <h2 className="text-cyan-400 font-bold text-lg mb-3">
                  {isDesignIntentMode ? "Design Intent Planner" : "Workflow Builder"} 
                </h2>

                {isDesignIntentMode && (
                  <button
                    onClick={onClose}
                    className="absolute top-4 right-4 text-slate-300 hover:text-white"
                    aria-label="Close"
                  >
                    ✕
                  </button>
                )}


                {coverage && (
                    <div
                        className={`absolute top-6 right-8 px-3 py-1 rounded-full text-xs font-semibold ${
                            coverage.total_score >= 80
                                ? "bg-green-600 text-white"
                                : coverage.total_score >= 60
                                ? "bg-yellow-500 text-black"
                                : "bg-red-600 text-white"
                        }`}
                    >
                        Spec Coverage: {coverage.total_score}%
                    </div>
                )}

                <textarea
                    className="w-full bg-slate-800 text-slate-200 rounded-md p-2"
                    rows={4}
                    value={refinedPrompt}
                    onChange={(e) => setRefinedPrompt(e.target.value)}
                    placeholder="Describe your design idea..."
                />
                {/* 🧩 DESIGN INTENT PLANNER PANEL */}
                {isDesignIntentMode && (
                  <div className="mt-4">
                    <h3 className="text-xl font-semibold text-emerald-400 mb-3">
                      Design Intent Planner – Round {roundNumber}
                    </h3>

                    {/* 📝 Current Understanding */}
                    <div className="mb-4">
                      <label className="block text-sm text-slate-400 mb-1">
                        Current Understanding
                      </label>
                    </div>

                    {/* 🔍 Loop Interpretation */}
                    {loopInterpretation && (
                      <div className="mb-4">
                        <p className="text-sm text-slate-400 mb-1">
                          Interpretation Across Domains
                        </p>
                        <ul className="text-xs text-slate-300 list-disc ml-4 space-y-1">
                          <li><strong>Digital:</strong> {loopInterpretation.digital}</li>
                          <li><strong>Embedded:</strong> {loopInterpretation.embedded}</li>
                          <li><strong>Analog:</strong> {loopInterpretation.analog}</li>
                          <li><strong>System:</strong> {loopInterpretation.system}</li>
                        </ul>
                      </div>
                    )}

                    {/* ❓ Clarifying Questions */}
                    <div className="space-y-3">
                      {clarifyQuestions.map((q, i) => (
                        <div key={i} className="bg-slate-800 p-3 rounded-md">
                          <p className="text-sm font-semibold text-slate-300 mb-1">
                            {i + 1}. {q}
                          </p>
                          <input
                            className="w-full bg-slate-900 text-slate-200 rounded-md px-2 py-1"
                            value={answers[q] || ""}
                            onChange={(e) => setAnswers({ ...answers, [q]: e.target.value })}
                            placeholder="Type or edit your answer"
                          />
                        </div>
                      ))}
                    </div>

                    {/* ⚙️ Footer Buttons */}
                    <div className="flex gap-3 mt-5 justify-end">
                      <button
                        onClick={handleContinueRound}
                        disabled={isLoadingRound}
                        className="bg-emerald-600 hover:bg-emerald-500 text-black font-semibold px-4 py-2 rounded"
                      >
                        {isLoadingRound ? "Thinking..." : "Continue Asking Questions"}
                      </button>
                      <button
                        onClick={handleFinalizeDesignIntent}
                        className="bg-cyan-600 hover:bg-cyan-500 text-black font-semibold px-4 py-2 rounded"
                      >
                        Done – Generate Final Spec
                      </button>
                    </div>
                  </div>
                )}


                {!isDesignIntentMode && coverage && (
                    <div className="mt-4 bg-slate-900 rounded-lg p-3 border border-slate-700">
                        <div className="w-full bg-gray-700 rounded-full h-2.5 mb-2">
                            <div
                                className={`h-2.5 rounded-full ${
                                    coverage.total_score >= 80
                                        ? "bg-green-500"
                                        : coverage.total_score >= 60
                                        ? "bg-yellow-400"
                                        : "bg-red-500"
                                }`}
                                style={{ width: `${coverage.total_score}%` }}
                            ></div>
                        </div>
                        <p className="text-sm text-slate-300">
                            Spec Coverage: {coverage.total_score}% (Intent {coverage.intent}, I/O {coverage.io}, Constraints {coverage.constraints}, Verification {coverage.verification})
                        </p>

                        {coverage.total_score < 80 && (
                            <p className="text-xs mt-1 text-yellow-400">
                                ⚠️ Recommended: Improve details or answer clarifying questions to reach ≥80% for best planning consistency.
                            </p>
                        )}

                        {clarifications.length > 0 && (
                            <div className="mt-2 text-xs text-slate-400">
                                <strong className="text-slate-200">🔍 Clarifying Questions:</strong>
                                <ul className="list-disc list-inside">
                                    {clarifications.map((q, i) => (
                                        <li key={i}>{q}</li>
                                    ))}
                                </ul>
                            </div>
                        )}
                    </div>
                )}

                {!isDesignIntentMode && plan?.missing_agents?.length > 0 && (
                    <div className="mt-4 bg-amber-900/40 border border-amber-600 rounded-lg p-3">
                        <h4 className="font-semibold text-amber-300">⚠️ Missing Agents</h4>
                        <ul className="list-disc list-inside text-sm text-amber-200">
                            {plan.missing_agents.map((a: string) => (
                                <li key={a}>{a}</li>
                            ))}
                        </ul>
                        <p className="text-xs mt-2 text-amber-300">
                            These agents don't exist yet. You can create them manually or click <strong>Auto-Compose Flow</strong> to let ChipLoop generate and register them automatically.
                        </p>
                    </div>
                )}

                {!isDesignIntentMode && plan && (
                    <div className="mt-4 bg-slate-900 rounded p-3 font-mono text-xs text-slate-200 overflow-auto max-h-64">
                        <pre>{JSON.stringify(plan, null, 2)}</pre>
                    </div>
                )}

                

               

                {/* Floating Notion Summary */}
                {!isDesignIntentMode && summary && (
                    <div className="absolute bottom-4 right-4 w-80 bg-gray-900 text-white p-4 rounded-xl shadow-lg">
                        <h3  className="font-bold text-sm mb-2">🧾 Spec Summary Preview</h3>
                        <pre className="text-xs whitespace-pre-wrap bg-gray-800 p-2 rounded-md max-h-48 overflow-auto">
                           {JSON.stringify(summary, null, 2)}
                        </pre>
                        <div className="mt-2">
                          <div className="w-full bg-gray-700 rounded-full h-2.5">
                             <div 
                                className={`h-2.5 rounded-full ${
                                coverage >= 80
                                  ? "bg-green-500"
                                  : coverage >= 60
                                  ? "bg-yellow-400"
                                  : "bg-red-500"
                                }`}
                                style={{ width: `${liveCoverage}%` }}
                             />
                          </div>
                          <p className="text-xs mt-1 text-gray-400">Coverage: {liveCoverage}%</p>
                        </div>
                    </div>
                )}
            </div>
        </div>
    );
}
