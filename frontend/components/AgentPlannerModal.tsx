"use client";

import React, { useState,useEffect } from "react";
import { useVoiceAnalyzer } from "@/hooks/useVoiceAnalyzer";


export default function AgentPlannerModal({ onClose }: { onClose: () => void }) {
  const [goal, setGoal] = useState("");
  const [agent, setAgent] = useState<any>(null);
  const [backendSource, setBackendSource] = useState("");
  const [loading, setLoading] = useState(false);
  const [isRecording, setIsRecording] = useState(false);
  const [mediaRecorder, setMediaRecorder] = useState<MediaRecorder | null>(null);
  const [summary, setSummary] = useState<any>(null);
  const [coverage, setCoverage] = useState(0);
  const [analyzing, setAnalyzing] = useState(false);

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
  
        await fetch("/api/voice_stream", {
          method: "POST",
          body: formData,
        });
      };
  
      rec.start();
      setMediaRecorder(rec);
      setIsRecording(true);
    } catch (err) {
      console.error("🎙️ Voice recording failed:", err);
    }
  }

  useEffect(() => {
    const handler = (e: any) => {
      const agentName = e.detail;
      fetch(`/api/agents/get_code?agent=${agentName}`)
        .then(r => r.text())
        .then(code => {
          setSelectedAgent(agentName);
          setAgentCode(code);
          setOpen(true);
        });
    };
    window.addEventListener("editAgent", handler);
    return () => window.removeEventListener("editAgent", handler);
  }, []);

  // --- Generate Agent Plan ---
  

  const handleAnalyzeSpec = async () => {
    setLoading(true);
    try {
      const res = await fetch("/api/analyze_spec", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ goal, user_id: "anonymous" }),
      });
      const data = await res.json();
      if (data.status === "ok") {
        setCoverage(data.coverage);
        alert(`✅ Spec analyzed: ${data.coverage.total_score}%`);
      }
    } catch (err) {
      alert("❌ Spec analysis failed");
    } finally {
      setLoading(false);
    }
  };
  const handleGenerateAgent = async () => {
    setLoading(true);
    try {
      const payload = coverage
        ? { goal, user_id: "anonymous", coverage }
        : { goal, user_id: "anonymous" };
      const res = await fetch("/api/plan_agent", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload),
      });
      const data = await res.json();
      setAgent(data.agent_plan);
      alert(`✅ Agent generated: ${data.agent_plan.agent_name}`);
  
      const agentName = prompt("💾 Enter name to save this agent:", data.agent_plan.agent_name);
      const loopType = prompt("🔁 Enter loop type (digital / analog / embedded / system):", "digital");
  
      if (agentName && loopType) {
        const saveRes = await fetch("/api/save_custom_agent", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({
            agent: {
              ...data.agent_plan,
              agent_name: agentName,
              domain: loopType,
            },
          }),
        });
        const saveData = await saveRes.json();
        alert(saveData.status === "ok" ? `💾 Agent "${agentName}" saved successfully!` : `⚠️ ${saveData.message}`);
      }
    } catch (err) {
      alert("❌ Agent generation failed.");
    } finally {
      setLoading(false);
    }
  };
  

  
  
  useEffect(() => {
    const ws = new WebSocket("/api/spec_live_feedback");
  
    ws.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        if (data.summary) setSummary(data.summary);
        if (data.coverage) setCoverage(data.coverage);
      } catch (err) {
        console.error("⚠️ Error parsing WebSocket data", err);
      }
    };
  
    ws.onclose = () => console.log("🔌 WebSocket closed");
    ws.onerror = (err) => console.error("⚠️ WS Error:", err);
  
    return () => ws.close();
  }, []);

  return (
    <div className="fixed inset-0 bg-black/70 flex items-center justify-center z-50">
      <div className="bg-slate-800 relative rounded-xl p-6 w-[600px] shadow-xl text-white">
        {/* Floating Spec Coverage Badge */}
        {agent?.coverage && (
          <div className="absolute top-4 right-6 bg-purple-600/80 text-xs px-2 py-1 rounded shadow-md">
            Coverage: {agent.coverage.total_score || 0}%
          </div>
        )}

        <div className="flex justify-between items-center mb-4">
          <h2 className="text-xl font-bold text-white">Agent Planner</h2>
          <button
            onClick={onClose}
            className="text-slate-400 hover:text-white transition"
          >
            ✖
          </button>
        </div>

        <p className="text-sm text-slate-400 mb-4">
          Enter a goal or description. The planner will analyze the spec,
          leverage memory, and design a new agent if required.
        </p>

        <textarea
          value={goal}
          onChange={(e) => setGoal(e.target.value)}
          placeholder="e.g., Design a 4-bit counter agent for RTL generation"
          className="w-full bg-slate-700 text-white rounded-lg p-3 text-sm outline-none focus:ring-2 focus:ring-cyan-400"
          rows={4}
        />

        <div className="flex gap-2 mt-4">

          <button
            onClick={handleAnalyzeSpec}
            disabled={analyzing || !goal.trim()}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            {analyzing ? "Analyzing..." : "Analyze Spec"}
          </button>




          <button
            onClick={handleGenerateAgent}
            disabled={loading || !goal.trim()}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            {loading ? "Planning..." : "Generate Missing Agent"}
          </button>

          <button
            onClick={handlePublish}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            Publish
          </button>


          <button
            onClick={startStopRecording}
            className={`bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition ${
              isRecording
                ? "bg-red-600 hover:bg-red-700 text-white animate-pulse"
                : "bg-purple-600 hover:bg-purple-700 text-white"
              }`}
          >
            🎙 {isRecording ? "Stop" : "Start"}
          </button>

          <button
            onClick={onClose}
            className="bg-slate-700 hover:bg-slate-600 px-3 py-1 rounded ml-auto"
          >
            Close
          </button>

        </div>

        {backendSource && (
          <p className="mt-3 text-xs text-slate-400">
            Source: <span className="text-slate-300">{backendSource}</span>
          </p>
        )}

        {/* Display Agent JSON */}
        {agent && (
          <div className="mt-6 bg-slate-900 p-4 rounded-lg text-xs font-mono text-slate-200 border border-slate-700">
            <div className="flex justify-between items-center mb-2">
              <h3 className="font-semibold text-slate-100">
                🧩 {agent.agent_name || "Unnamed Agent"}
              </h3>
            </div>

            {agent.coverage && (
              <>
                <div className="mb-2 text-xs text-slate-400">
                  Spec Coverage: {agent.coverage.total_score}% (Intent{" "}
                  {agent.coverage.intent_score}, I/O{" "}
                  {agent.coverage.io_score}, Constraints{" "}
                  {agent.coverage.constraint_score})
                </div>
                <div className="w-full bg-slate-700 h-1.5 rounded mb-3">
                  <div
                    className={`h-1.5 rounded ${
                      agent.coverage.total_score >= 80
                        ? "bg-green-500"
                        : agent.coverage.total_score >= 60
                        ? "bg-yellow-400"
                        : "bg-red-500"
                    }`}
                    style={{ width: `${agent.coverage.total_score}%` }}
                  ></div>
                </div>
              </>
            )}

            <pre className="whitespace-pre-wrap text-slate-300">
              {JSON.stringify(agent, null, 2)}
            </pre>
          </div>
        )}
        
        {summary && (
          <div className="absolute bottom-4 right-4 w-80 bg-gray-900 text-white p-4 rounded-xl shadow-lg">
              <h3 className="font-bold text-sm mb-2">🧾 Spec Summary Preview</h3>
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
                    style={{ width: `${coverage}%` }}
                  />
                </div>
                <p className="text-xs mt-1 text-gray-400">Coverage: {coverage}%</p>
              </div>
          </div>
        )}
      
      </div>
    </div>
  );
}
