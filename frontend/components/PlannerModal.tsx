"use client";
import { useState, useEffect } from "react";
import { useVoiceAnalyzer } from "@/hooks/useVoiceAnalyzer";

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
            await fetch("/api/voice_stream", {
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
                body: JSON.stringify({ goal }),
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
      
            if (workflowName) {
              await fetch("/api/save_custom_workflow", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({
                  workflow: {
                    workflow_name: workflowName,
                    loop_type: loopType.toLowerCase(),
                    nodes: data.nodes,
                    edges: data.edges,
                    summary: data.summary,
                  },
                  user_id: "anonymous",
                  is_custom: true,
                }),
              });
      
              alert(
                `💾 Workflow "${workflowName}" saved under "${loopType}" Custom Workflows.`
              );
            }
      
            // ✅ Save locally for instant reload
            const stored = { nodes: data.nodes, edges: data.edges };
            localStorage.setItem(
              `workflow_${workflowName}`,
              JSON.stringify(stored)
            );
      
            alert(`✅ Auto-composed workflow:\n${data.summary}`);
            alert("✅ Auto-Compose complete!\n🔍 Missing Agents → Auto-created if required.");
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

    return (
        <div className="fixed inset-0 bg-black/70 flex items-center justify-center z-50">
            <div className="bg-slate-800 relative rounded-xl p-6 w-[600px] shadow-xl text-white">
                <h2 className="text-cyan-400 font-bold text-lg mb-3">
                    AI Workflow Planner
                </h2>

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
                    value={goal}
                    onChange={(e) => setGoal(e.target.value)}
                    placeholder="Describe your design goal..."
                    className="w-full h-24 p-2 bg-slate-900 rounded border border-slate-700 text-sm text-slate-200 focus:ring-1 focus:ring-cyan-500"
                />

                <div className="mt-3 flex gap-2 flex-wrap">
                    <button
                        onClick={handleAnalyzeSpec}
                        disabled={analyzing || !goal.trim()}
                        className="bg-cyan-700 hover:bg-cyan-600 px-3 py-1 rounded disabled:opacity-50"
                    >
                        {analyzing ? "Analyzing..." : "Analyze Spec"}
                    </button>

                    <button
                        onClick={handlePlan}
                        disabled={loading || !goal.trim()}
                        className="bg-cyan-700 hover:bg-cyan-600 px-3 py-1 rounded disabled:opacity-50"
                    >
                        {loading ? "Generating..." : "Generate Plan"}
                    </button>

                    <button
                        onClick={handleAutoCompose}
                        disabled={autoLoading || !goal.trim()}
                        className="bg-cyan-700 hover:bg-cyan-600 px-3 py-1 rounded disabled:opacity-50"
                    >
                        {autoLoading ? "Composing..." : "Auto-Compose Flow"}
                    </button>

                    {/* 🎙 Voice Mode Toggle */}
                    <button
                        onClick={toggleVoiceMode}
                        className={`ml-4 px-3 py-2 rounded-full ${
                        isRecording ? "bg-green-600 hover:bg-yellow-700" : "bg-gray-700 hover:bg-red-600"
                        } text-white`}
                        title={isRecording ? "Voice Mode Active" : "Start Voice Mode"}
                    >
                    🎙
                    </button>
                    
                    <button
                        onClick={onClose}
                        className="bg-slate-700 hover:bg-slate-600 px-3 py-1 rounded ml-auto"
                    >
                        Close
                    </button>
                </div>

                {coverage && (
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

                {plan?.missing_agents?.length > 0 && (
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

                {plan && (
                    <div className="mt-4 bg-slate-900 rounded p-3 font-mono text-xs text-slate-200 overflow-auto max-h-64">
                        <pre>{JSON.stringify(plan, null, 2)}</pre>
                    </div>
                )}

                {/* Floating Notion Summary */}
                {summary && (
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
