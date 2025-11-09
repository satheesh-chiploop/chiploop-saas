"use client";

import React, { useState,useEffect } from "react";
import { useVoiceAnalyzer } from "@/hooks/useVoiceAnalyzer";
import { Special_Elite } from "next/font/google";
import MissingAgentNamingDialog from "./MissingAgentNamingDialog";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
const supabase = createClientComponentClient();
import WorkflowConsole from "@/app/workflow/WorkflowConsole";


function getValueFromSpec(obj, path) {
  try {
    return path
      .replace(/\]/g, "")
      .split(/\.|\[/)
      .reduce((o, k) => (o ? o[k] : undefined), obj);
  } catch {
    return undefined;
  }
}


export default function AgentPlannerModal({ onClose }: { onClose: () => void }) {
  const [goal, setGoal] = useState("");
  const [agent, setAgent] = useState<any>(null);
  const [backendSource, setBackendSource] = useState("");
  const [loading, setLoading] = useState(false);
  const [isRecording, setIsRecording] = useState(false);
  const [mediaRecorder, setMediaRecorder] = useState<MediaRecorder | null>(null);
  const [summary, setSummary] = useState<any>(null);
  const [coverage, setCoverage] = useState(0);
  const [isSelectingAgents, setIsSelectingAgents] = useState(false);
  const [selectedAgents, setSelectedAgents] = useState<string[]>([]);
  const [missingAgents, setMissingAgents] = useState<string[]>([]);
  const [isAnalyzing, setIsAnalyzing] = useState(false);
  const [isGeneratingAgent, setIsGeneratingAgent] = useState(false);
  const [spec, setSpec] = useState<any>(null);
  const [missingFields, setMissingFields] = useState([]);
  const [readyForPlanning, setReadyForPlanning] = useState(false);
  const [fieldEdits, setFieldEdits] = useState({});
  const [improvedSpec, setImprovedSpec] = useState<string | null>(null);
  const [finalizedSpec, setFinalizedSpec] = useState<string | null>(null);
  const [result, setResult] = useState<any>(null);
  const [missingFieldEdits, setMissingFieldEdits] = useState({});
  const [preplan, setPreplan] = useState(null);
  const [stage, setStage] = useState<"initial" | "analyzed" | "autofill" | "finalized" | "workflow">("initial");
  const [showNamingDialog, setShowNamingDialog] = useState(false);
  const [namingTargets, setNamingTargets] = useState<string[]>([]);
  // ADD this new state near your other state declarations:
  const [workflowGraph, setWorkflowGraph] = useState<any | null>(null);
  const [finalAgents, setFinalAgents] = useState<string[]>([]);
  const [recentlyGenerated, setRecentlyGenerated] = useState<string[]>([]);

  const handlePublish = () => {
    console.log("⚠️ Publish is not implemented yet. Coming in Step 7.");
  };
  function normalizeMissing(input) {
    return (input || []).map(m =>
      typeof m === "string"
        ? m                     // ✅ keep raw strings as strings
        : m                     // ✅ keep dict objects untouched
    );
  }
 // function normalizeMissing(input) {
  //  return (input || []).map(m =>
  //    typeof m === "string" ? { path: m, ask: "", type: "text" } : m
 //   );
 // }
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
    setIsAnalyzing(true);
    try {
      const res = await fetch("/api/analyze_spec", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ goal, user_id: "anonymous" }),
      });
  
      const data = await res.json();
      console.log("DEBUG ANALYZE SPEC RESPONSE:", data);
  
      const result = data?.result ?? data;
      setResult(result);



      if (result.structured_spec_final) {
        setSpec(result.structured_spec_final);
        setCoverage(result.coverage ?? result.coverage?.total_score ?? 0);
        setMissingFields([]);
        setReadyForPlanning(true);
        setResult(null);
        return;
      } else if (result.structured_spec_draft) {
        setSpec(result.structured_spec_draft);
        setCoverage(result.coverage ?? result.coverage?.total_score ?? 0);
        const missingList = normalizeMissing(result.missing ?? []);
        
        setMissingFields(missingList);

        setReadyForPlanning(false);
        return;
      }

    } catch (err) {
      console.error(err);
      alert("❌ Analyze Spec failed");
    } finally {
      setIsAnalyzing(false);
      setStage("analyzed");
    }

  };
  const handleSelectAgents = async () => {
    if (!goal.trim()) return;
    setIsSelectingAgents(true);
    

  
    try {

      const { data: { session } } = await supabase.auth.getSession();
      const user_id = session?.user?.id || "anonymous";

      console.log("🟢 Supabase session check:", session);
      console.log("🟢 Supabase session check:", user_id);
      const res = await fetch("/api/plan_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(
          spec
            ? { prompt: goal, structured_spec_final: spec,user_id } // now spec is not null 🎯
            : { prompt: goal,user_id }
        ),
      });
  
      const data = await res.json();
      const plan = data.plan || {};
  
      setPreplan(plan);
  
      setSelectedAgents(plan.agents ?? []);
      setMissingAgents(plan.missing_agents ?? []);

    
        // ✅ No missing → This is the final agent set
      setFinalAgents(plan.agents ?? []);
      setRecentlyGenerated([]); // none generated yet
      
  
    } catch (err) {
      console.error(err);
      alert("❌ Select Agents failed");
    }
    
    setIsSelectingAgents(false);
  };
  
  const handleGenerateMissingAgents = async () => {
    try {
      // Case 1: User did NOT run Select Agents yet → compute missing agents automatically
      if ((!preplan || !preplan.missing_agents || preplan.missing_agents.length === 0) && spec) {
        const res = await fetch("/api/plan_workflow", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({
            prompt: goal,
            structured_spec_final: spec,
          }),
        });
  
        const data = await res.json();
        const newPlan = data.plan || data;
  
        setPreplan(newPlan);
        setMissingAgents(newPlan.missing_agents || []);
  
        // 👇 Open naming dialog with missing agents
        setNamingTargets(newPlan.missing_agents || []);
        setShowNamingDialog(true);
        return;
      }
  
      // Case 2: User already ran Select Agents → just open naming dialog
      setNamingTargets(missingAgents);
      setShowNamingDialog(true);

      window.dispatchEvent(new Event("refreshAgents"));

  
    } catch (err) {
      console.error("❌ Setup for Generate Missing Agents failed:", err);
      alert("❌ Could not determine missing agents.");
    }
  };
  
  


  const handleFinalizeSpec = async () => {
    if (!goal.trim()) return;
  
    setIsAnalyzing(true);
    try {
      const res = await fetch("/api/finalize_spec_natural_sentences", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          original_text: goal,
          improved_text: improvedSpec,
          structured_spec_draft: JSON.parse(JSON.stringify(spec)),
          edited_values: {...missingFieldEdits},
          missing: JSON.parse(JSON.stringify(missingFields)),
          user_id: null,
        }),
      });
  
      const data = await res.json();

      console.group("🧪 FINALIZE PAYLOAD");
      console.log("spec?", spec && Object.keys(spec || {}).length, spec);
      console.log("missingFields:", missingFields);
      console.log("edited_values:", missingFieldEdits);
      console.log("improvedSpec?", !!improvedSpec);
      console.groupEnd();
  
      // ✅ Store natural language final spec
      setFinalizedSpec(data.final_text);
      setGoal(data.final_text);
  
      // ✅ Store machine spec
      setSpec(data.structured_spec_final);


      /* ✅ Normalize & update missing list correctly */
      const remaining = normalizeMissing(data.remaining_missing ?? []);
      setMissingFields(remaining);
  
      // ✅ Extract correct coverage

      const cov = data.coverage ?? data.coverage_final ?? 0;
      setCoverage(typeof cov === "object" ? (cov.total_score ?? 0) : cov);
  
  
      // ✅ ★ KEY FIX ★ Stop UI returning to auto-fill panel
      setResult(null);
      // setMissingFields([]);
      setMissingFieldEdits({});
      setImprovedSpec(null);
  
      // ✅ Enable Select Agents
      //setReadyForPlanning(true);
      setReadyForPlanning(remaining.length === 0);
  
    } catch (err) {
      console.error("❌ Finalize Spec failed:", err);
    }
    setIsAnalyzing(false);
    setStage("finalized");
  };
  const handleAutoFillMissingFields = async () => {
    if (!spec) return;
  
    setIsAnalyzing(true);
    try {
      const res = await fetch("/api/auto_fill_missing_fields", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          structured_spec_draft: spec,
          missing: missingFields,
          original_text: goal,   
        })
      }).then(r => r.json());

  
      // ✅ Natural language preview text (just preview, do NOT overwrite goal)
      setImprovedSpec(res.improved_text ?? null);
  
      // ✅ Structured spec from backend (if inferred)
      if (res.structured_spec_enhanced) setSpec(res.structured_spec_enhanced);
  
      // ✅ SAFELY extract missing fields (works whether objects OR strings)
      const remaining = normalizeMissing(res.remaining_missing_fields ?? missingFields);
      setMissingFields(remaining);

      const autoVals = res.auto_filled_values ?? {};

      function resolveAutoValue(path: string, autoVals: any) {
        const leaf = path.split(".").pop().replace(/\[\d+\]/g, "");
        return (
          autoVals[path] ??
          autoVals[leaf] ??
          autoVals[leaf.toLowerCase()] ??
          ""
        );
      }
      
      setMissingFieldEdits(
        Object.fromEntries(
          remaining.map((m: any) => [m.path, resolveAutoValue(m.path, autoVals)])
        )
      );
      
      // ✅ Switch UI to edit panel
      setStage("autofill");

  
    } catch (err) {
      console.error("❌ Auto-fill failed:", err);
    } finally {
      setIsAnalyzing(false);
    }
  };
  
    // NEW: Build Workflow (Step 3)
  const handleBuildWorkflow = async () => {
    try {
      // Ensure we have a user_id (your Select step already uses Supabase)
      const { data: { session } } = await supabase.auth.getSession();
      const user_id = session?.user?.id || "anonymous";

      if (!finalAgents || finalAgents.length === 0) {
        alert("Please run Select Agents first (or add at least one agent).");
        return;
      }

      const res = await fetch("/api/build_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          user_id,
          agents: finalAgents, // ← reuse from Step 2
        }),
      });

      if (!res.ok) {
        const msg = await res.text();
        throw new Error(msg || "Build workflow failed.");
      }

      const data = await res.json();
      // Expecting { workflow: { nodes: [...], edges: [...], ... } }
      setWorkflowGraph(data.workflow);
      setStage("workflow");

    } catch (err) {
      console.error("❌ Build Workflow failed:", err);
      alert(`❌ Build Workflow failed: ${String(err)}`);
    }
  };
  useEffect(() => {
    const ws = new WebSocket("/spec_live_feedback");
  
    ws.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        if (data.summary) setSummary(data.summary);
        if (data.coverage) setCoverage(data.coverage.total_score);
        else if (data.result?.coverage) setCoverage(data.result.coverage.total_score);
      } catch (err) {
        console.error("⚠️ Error parsing WebSocket data", err);
      }
    };
  
    ws.onclose = () => console.log("🔌 WebSocket closed");
    ws.onerror = (err) => console.error("⚠️ WS Error:", err);
  
    return () => ws.close();
  }, []);

  useEffect(() => {
    if (stage === "workflow" && workflowGraph) {
      console.log("📡 Dispatching workflow graph to canvas:", workflowGraph);
      window.dispatchEvent(
        new CustomEvent("loadWorkflowGraph", { detail: workflowGraph })
      );
      onClose(); // ✅ Close the System Planner modal when done
    }
  }, [stage, workflowGraph, onClose]);

  return (
    <div className="fixed inset-0 bg-black/70 flex items-center justify-center z-50">
      <div className="bg-slate-800 relative rounded-xl p-6 w-[800px] shadow-xl text-white">
        {/* Floating Spec Coverage Badge */}
        {stage === "analyzed" && coverage !== null && coverage !== undefined && (
          <div className="absolute top-4 right-6 bg-purple-600/80 text-xs px-2 py-1 rounded shadow-md">
            Coverage: {coverage || 0}%
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
          value={finalizedSpec ?? goal}
          onChange={(e) => {
            if (finalizedSpec !== null) setFinalizedSpec(e.target.value);
            else if (improvedSpec !== null) setImprovedSpec(e.target.value);
            else setGoal(e.target.value);
          }}
          placeholder="e.g., Design a 4-bit counter agent for RTL generation"
          className="w-full bg-slate-700 text-white rounded-lg p-3 text-sm outline-none focus:ring-2 focus:ring-cyan-400"
          rows={4}
        />

        <div className="flex gap-2 mt-4">

          <button
            onClick={handleAnalyzeSpec}
            disabled={isAnalyzing  || !goal.trim()}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            {isAnalyzing ? "Analyzing..." : "Analyze Spec"}
          </button>



          <button
            onClick={handleSelectAgents}
            disabled={!goal.trim() || isSelectingAgents}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            {isSelectingAgents? "Selecting Agents..." : "Select Agents"}
          </button>


          <button
            onClick={handleGenerateMissingAgents}
            disabled={isGeneratingAgent || !goal.trim()}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            {isGeneratingAgent  ? "Planning..." : "Generate Missing Agent"}
          </button>

          <button
            onClick={handleBuildWorkflow}
            disabled={missingAgents.length > 0 || finalAgents.length === 0}
            className="bg-cyan-600 hover:bg-cyan-500 text-white text-sm px-4 py-2 rounded disabled:opacity-40 transition"
          >
            Build Workflow
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


        {/* Show missing fields simply */}
        {!finalizedSpec && missingFields.length > 0 && (
          <div className="mt-3 text-yellow-400 text-sm">
            Missing Details ({missingFields.length}):
            <ul className="list-disc pl-6">
             {missingFields.map((m, idx) => (
              <li key={idx}>{m.path}</li>
             ))}
            </ul>
          </div>
        )}
        {/* Auto-Fill Button */}
        {!finalizedSpec && missingFields.length > 0  && (
          <button
            className="mt-3 px-4 py-2 rounded-lg bg-yellow-500 text-black font-semibold"
            onClick={handleAutoFillMissingFields}        
          >
            Auto-Fill Missing Details
          </button>
        )}
        {stage === "autofill" && missingFields.length > 0 && (
         <div className="mt-4 border border-yellow-500 p-3 rounded-md bg-yellow-900/30">
          <h3 className="text-yellow-300 font-semibold mb-2">
            Review & Edit Auto-Filled Values
          </h3>

          <table className="w-full text-sm">
            <tbody>
              {missingFields.map((item, idx) => (
                <tr key={idx}>
                  <td className="py-1 pr-2 text-gray-200">{item.path}</td>
                  <td className="py-1">
                    <input
                      className="w-full bg-gray-800 text-white border border-gray-600 rounded px-2 py-1"
                      value={missingFieldEdits[item.path] ?? ""}
                      onChange={(e) =>
                        setMissingFieldEdits({
                          ...missingFieldEdits,
                          [item.path]: e.target.value,
                        })
                      }
                    />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
         </div>
        )}

        {/* Finalize Spec Button */}
        {stage === "autofill" && (
          <button
            className="mt-3 px-4 py-2 rounded-lg bg-green-500 text-black font-semibold"
            onClick={handleFinalizeSpec}
          >
            Finalize Spec
          </button>
        )}

        {/* NEW: Workflow Canvas stage */}
        
        
        {missingAgents.length > 0 && (
          <div className="mt-4 border border-cyan-700 rounded-lg p-3 bg-slate-800/60">
            <p className="text-cyan-300 text-sm font-semibold mb-2">Detected Agents:</p>
            <p className="text-green-400 text-xs mb-1">Required Agents:</p>
            <ul className="ml-4 mb-2">
              {(finalAgents.length > 0 ? finalAgents : selectedAgents).map(a => (
                <li key={a} className="text-green-300 text-xs">• {a}</li>
              ))}
            </ul>
            <p className="text-yellow-400 text-xs mb-1">Missing Agents:</p>
            <ul className="ml-4">
              {missingAgents.length > 0
                ? missingAgents.map(a => (
                   <li key={a} className="text-yellow-300 text-xs">• {a}</li>
                  ))
                : <li className="text-gray-400 text-xs">None 🎉</li>
              }
            </ul>
          </div>
        )}

        {missingAgents.length === 0 && finalAgents.length > 0 && (
          <div className="mt-6 border border-cyan-700 rounded-lg p-3 bg-slate-800/60">
            <p className="text-cyan-300 text-sm font-semibold mb-2">
              ✅ Final Agents for Workflow:
            </p>

            <ul className="ml-4 mb-3 space-y-0.5">
              {finalAgents.map(a => (
                <li key={a} className="text-green-300 text-xs">• {a}</li>
              ))}
            </ul>

            {recentlyGenerated.length > 0 && (
              <div className="bg-green-900/30 border border-green-600 rounded p-2 mt-2">
                <p className="text-green-400 text-xs font-medium mb-1">
                  🟢 Generated in this step:
                </p>
                <ul className="ml-4 space-y-0.5">
                  {recentlyGenerated.map(a => (
                    <li key={a} className="text-green-300 text-xs">+ {a}</li>
                  ))}
                </ul>
              </div>
            )}


          </div>
        )}


        {stage === "analyzed" && coverage !== null && (
          <div className="mt-4 bg-slate-900 rounded-lg p-3 border border-slate-700">
            <div className="w-full bg-gray-700 rounded-full h-2.5 mb-2">
              <div
                className={`h-2.5 rounded-full ${
                  coverage >= 80
                   ? "bg-green-500"
                   : coverage >= 60
                   ? "bg-yellow-400"
                   : "bg-red-500"
                }`}
                style={{ width: `${coverage}%` }}
              ></div>
            </div>
            <p className="text-sm text-slate-300">Spec Coverage: {coverage}%</p>
          </div>
        )}
             
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


            {stage === "analyzed" && coverage !== null && (
              <div className="absolute top-4 right-6 bg-purple-600/80 text-xs px-2 py-1 rounded shadow-md">
                Spec Coverage: {coverage}%
              </div>
            )}

            
            <pre className="whitespace-pre-wrap text-slate-300">
              {JSON.stringify(agent, null, 2)}
            </pre>
          </div>
        )}
        {showNamingDialog && (
          <MissingAgentNamingDialog
            missingAgents={namingTargets}
            domain={(spec?.loop_type || "digital").toLowerCase()}
            onCancel={() => setShowNamingDialog(false)}
            onConfirm={async (finalNames) => {
              setShowNamingDialog(false);
              setIsGeneratingAgent(true);
            
              try {
                const { data: { session } } = await supabase.auth.getSession();
                const user_id = session?.user?.id;
                const res = await fetch("/api/generate_missing_agents_batch", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify({
                    goal,
                    user_id: user_id,
                    agent_names: finalNames,
                    structured_spec_final: spec
                  })
                }).then(r => r.json());
            
                // Append new agents to local custom agent list
                const existing = JSON.parse(localStorage.getItem("custom_agents") || "[]");
                const newOnes = (res.generated_agents || []).map(a => ({
                  agent_name: a.agent_name,
                  loop_type: a.loop_type,
                  script_path: a.path,
                  description: a.description,
                  is_custom: true
                }));
                localStorage.setItem("custom_agents", JSON.stringify([...existing, ...newOnes]));
            
                // Trigger UI refresh event
                window.dispatchEvent(new Event("refreshAgents"));
            
                alert("✅ Missing agents successfully generated!");
                // Extract actual generated agent names
                const generatedAgents = (res.generated_agents || []).map(a => a.agent_name);

                // ✅ Add generated agents into selectedAgents + finalAgent list
                setSelectedAgents(prev => [...prev, ...generatedAgents]);
                setFinalAgents(prev => [...prev, ...generatedAgents]);

                // ✅ Track for UI highlighting
                setRecentlyGenerated(generatedAgents);

                // ✅ Clear missing list, they are resolved
                setMissingAgents([]);

                setPreplan(prev => ({ ...prev, missing_agents: [] }));


                // ✅ Small visual cue
                alert("✅ Missing agents resolved! You can now Build Workflow.");

            
              } catch (err) {
                console.error(err);
                alert("❌ Failed to generate missing agents");
              }
            
              setIsGeneratingAgent(false);
            }}
          />
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
