"use client";
// 10-15
import React, { useCallback, useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { getStableUserId } from "@/utils/userId"

import ReactFlow, {
  addEdge,
  Background,
  Controls,
  MiniMap,
  useEdgesState,
  useNodesState,
  Connection,
  Edge,
  Node,
  ReactFlowProvider,
  useReactFlow,
} from "reactflow";
import "reactflow/dist/style.css";
const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
import AgentNode from "./AgentNode";
import WorkflowConsole from "./WorkflowConsole";
import PlannerModal from "@/components/PlannerModal";
import AgentPlannerModal from "@/components/AgentPlannerModal";
/* =========================
   Types & Constants
========================= */
type LoopKey = "digital" | "analog" | "embedded" | "system";
type AgentNodeData = { uiLabel: string; backendLabel: string; desc?: string };

type CatalogItem = { uiLabel: string; backendLabel: string; desc?: string };

if (typeof window !== "undefined" && !localStorage.getItem("anon_user_id")) {
  localStorage.setItem("anon_user_id", crypto.randomUUID());
}

const LOOP_AGENTS: Record<LoopKey, CatalogItem[]> = {
  digital: [
    { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent", desc: "Capture design spec & I/Os" },
    { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent", desc: "Generate synthesizable RTL" },
    { uiLabel: "Verification Agent", backendLabel: "Digital Testbench Agent", desc: "Create TB & assertions" },
    { uiLabel: "Sim Agent", backendLabel: "Digital Sim Agent", desc: "Compile & simulate" },
  ],
  analog: [
    { uiLabel: "Spec Agent", backendLabel: "Analog Spec Agent", desc: "Analog specs & targets" },
    { uiLabel: "Netlist Agent", backendLabel: "Analog Netlist Agent", desc: "Schematic/topology" },
    { uiLabel: "Sim Agent", backendLabel: "Analog Sim Agent", desc: "SPICE/AMS runs" },
    { uiLabel: "Result Agent", backendLabel: "Analog Result Agent", desc: "Summarize results" },
  ],
  embedded: [
    { uiLabel: "Spec Agent", backendLabel: "Embedded Spec Agent", desc: "Firmware/SoC reqs" },
    { uiLabel: "Code Agent", backendLabel: "Embedded Code Agent", desc: "Drivers & firmware" },
    { uiLabel: "Sim Agent", backendLabel: "Embedded Sim Agent", desc: "Run harness / co-sim" },
    { uiLabel: "Result Agent", backendLabel: "Embedded Result Agent", desc: "Summarize outputs" },
  ],
  system: [
    { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent", desc: "System-level digital spec" },
    { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent", desc: "Digital IP RTL design" },
    { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent", desc: "Embedded driver / firmware" },
    { uiLabel: "Sim Agent", backendLabel: "Embedded Sim Agent", desc: "Firmware simulation harness" },
    { uiLabel: "Result Agent", backendLabel: "Embedded Result Agent", desc: "Summarize hardware + firmware integration" },
  ],
};
//const [showPlanner, setShowPlanner] = useState(false);

//{showPlanner && <PlannerModal onClose={() => setShowPlanner(false)} />}
/* =========================
   Page Wrapper
========================= */
export default function WorkflowPageWrapper() {
  return (
    <ReactFlowProvider>
      <WorkflowPage />
    </ReactFlowProvider>
  );
}

/* =========================
   Main Page
========================= */
function WorkflowPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const rf = useReactFlow();

  // core state
  const [loop, setLoop] = useState<LoopKey>("digital");
  const [nodes, setNodes, onNodesChange] = useNodesState<Node<AgentNodeData>>([]);
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge[]>([]);
  const [jobId, setJobId] = useState<string | null>(null);

  // local catalog states
  const [customAgents, setCustomAgents] = useState<CatalogItem[]>([]);
  const [customWorkflows, setCustomWorkflows] = useState<string[]>([]);
  const [loadingAgents, setLoadingAgents] = useState(true);
  const [loadingWorkflows, setLoadingWorkflows] = useState(true);
  
  // modals
  const [showSpecModal, setShowSpecModal] = useState(false);
  const [showCreateAgentModal, setShowCreateAgentModal] = useState(false);
  const [showPlanner, setShowPlanner] = useState(false);
  const [showAgentPlanner, setShowAgentPlanner] = useState(false);

  const {fitView} = useReactFlow();

  const [contextMenu, setContextMenu] = useState<{x:number; y:number; name:string} | null>(null);
  const [renameTarget, setRenameTarget] = useState<{oldName:string, newName:string}>({oldName:"", newName:""});
  
  const openContextMenu = (e: React.MouseEvent, name: string) => {
    e.preventDefault();
    setContextMenu({ x: e.clientX, y: e.clientY, name });
  };
  
  const closeContextMenu = () => setContextMenu(null);
  
  const deleteCustomWorkflow = async (name: string) => {
    try {
      const userId = await getStableUserId(supabase);  // ✅ unified ID

      const res = await fetch(`${API_BASE}/delete_custom_workflow?name=${encodeURIComponent(name)}&user_id=${userId}`, {
        method: "DELETE"
      });

      const j = await res.json();
      if (j.status !== "ok") {
        alert("Delete failed");
        return;
      }

      await loadCustomWorkflowsFromDB();  // ✅ refresh sidebar list
    } catch (err) {
      console.error("Delete failed", err);
      alert("❌ Could not delete workflow.");
    } finally {
      closeContextMenu();
    }
  };
  
  const renameCustomWorkflow = async () => {
    try {
      if (!renameTarget.newName.trim()) {
        alert("Enter a valid new name.");
        return;
      }
      // local optimistic update
      const oldKey = `workflow_${renameTarget.oldName}`;
      const newKey = `workflow_${renameTarget.newName}`;
  
      const cached = localStorage.getItem(oldKey);
      if (cached) {
        localStorage.removeItem(oldKey);
        localStorage.setItem(newKey, cached);
      }
      setCustomWorkflows((prev) =>
        prev.map((n) => (n === renameTarget.oldName ? renameTarget.newName : n))
      );
  
      // backend rename
      const res = await fetch(`${API_BASE}/rename_custom_workflow`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(renameTarget),
      });
      const j = await res.json();
      if (j.status !== "ok") {
        alert(`⚠️ Rename failed: ${j.message || "Unknown error"}`);
        await loadCustomWorkflowsFromDB();
        return;
      }
  
      await loadCustomWorkflowsFromDB();
    } catch (err) {
      console.error("Rename failed", err);
      alert("❌ Could not rename workflow.");
    } finally {
      setRenameTarget({ oldName: "", newName: "" });
      closeContextMenu();
    }
  };
  
  // NEW: agent context menu state
  const [agentMenu, setAgentMenu] = useState<{ x: number; y: number; name: string } | null>(null);

  const openAgentMenu = (e: React.MouseEvent, name: string) => {
    e.preventDefault();
    setAgentMenu({ x: e.clientX, y: e.clientY, name });
  };
  const closeAgentMenu = () => setAgentMenu(null);

// NEW: API calls
  const renameCustomAgent = async (oldName: string) => {
    const newName = prompt("New agent name:", oldName) || "";
    if (!newName || newName === oldName) return;
    const res = await fetch(`${API_BASE}/rename_custom_agent`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ old_name: oldName, new_name: newName }),
    });
    const j = await res.json();
    if (j.status !== "ok") {
      alert(`⚠️ Rename failed: ${j.message || "Unknown error"}`);
    } else {
      window.dispatchEvent(new Event("refreshAgents")); // reuse your existing refresh pattern
    }
    closeAgentMenu();
  };

  const deleteCustomAgent = async (name: string) => {
    const userId = await getStableUserId(supabase);  // ✅ unify ID

    const res = await fetch(`${API_BASE}/delete_custom_agent?name=${encodeURIComponent(name)}&user_id=${userId}`, {
      method: "DELETE"
    });

    const j = await res.json();
    if (j.status !== "ok") {
      alert(`Delete failed: ${j.message}`);
      return;
    }

    window.dispatchEvent(new Event("refreshAgents"));
    window.dispatchEvent(new Event("refreshWorkflows"));
    closeAgentMenu();
  };

  // 🔁 Ensure sidebar visible once agents/workflows are loaded
  useEffect(() => {
    if (customAgents.length > 0 || customWorkflows.length > 0) {
      setLoadingAgents(false);
      setLoadingWorkflows(false);
    }
  }, [customAgents, customWorkflows]);

  const anonUserId =
    typeof window !== "undefined"
      ? localStorage.getItem("anon_user_id")
      : "anonymous";
  
  useEffect(() => {
    if (nodes.length > 0 || edges.length > 0) {
      fitView({ padding: 0.15, duration: 500 });
    }
  }, [nodes, edges, fitView]);
  
  // workflow console tab state
  const [activeTab, setActiveTab] = useState<"summary" | "live" | "output">("summary");

  /* ---------- Auth gate ---------- */
  useEffect(() => {
    (async () => {
      setLoadingAgents(true);
      setLoadingWorkflows(true);
  
      const { data: { session } } = await supabase.auth.getSession();
      if (!session) {
        router.push("/login");
        return;
      }
  
      try {
        
        const savedWF = Object.keys(localStorage).filter((k) => k.startsWith("workflow_"));
        // ✅ Load custom agents per user from Supabase
        const { data: { session } } = await supabase.auth.getSession();
        const userId = session?.user?.id || localStorage.getItem("anon_user_id") || "anonymous";

        const { data } = await supabase
          .from("agents")
          .select("*")
          .eq("owner_id", userId)
          .order("created_at", { ascending: false });

        setCustomAgents(
            (data || []).map(a => ({
              uiLabel: a.agent_name,
              backendLabel: a.agent_name,
              desc: a.description || "",
            }))
        );
        setCustomWorkflows(savedWF.map((k) => k.replace("workflow_", "")));
  
        // Load from Supabase after local cache
        setTimeout(() => loadCustomWorkflowsFromDB(), 600);
      } catch (err) {
        console.error("❌ Error loading user or workflows:", err);
      } finally {
        setLoadingAgents(false);
        setLoadingWorkflows(false);
      }
    })();
  }, [supabase, router]);

  // 🔁 Listen for new workflows saved by PlannerModal
  // 🔁 Listen for global refresh events (Planner or Save)
  useEffect(() => {
    const refreshHandler = () => {
      console.log("🔄 Refreshing workflows (global trigger)");
      loadCustomWorkflowsFromDB();
    };
    window.addEventListener("refreshWorkflows", refreshHandler);
    return () => window.removeEventListener("refreshWorkflows", refreshHandler);
  }, []);

  useEffect(() => {
    const handler = (e: any) => {
      const graph = e.detail;
      if (!graph) return;
  
      console.log("🎯 Received workflow graph from System Planner:", graph);
  
      // Normalize nodes to match ReactFlow agentNode structure
      const newNodes = (graph.nodes || []).map((n: any, idx: number) => ({
        id: n.id || `n${idx}`,
        type: "agentNode",
        position: n.position || { x: 120 * idx, y: 200 },
        data: {
          uiLabel: n.data?.uiLabel || n.data?.backendLabel || n.label || "Agent",
          backendLabel: n.data?.backendLabel || n.data?.uiLabel || n.label || "Unknown Agent",
          desc: n.data?.desc || "",
        },
      }));
  
      const newEdges = (graph.edges || []).map((e: any, idx: number) => ({
        id: e.id || `e${idx}`,
        source: e.source,
        target: e.target,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      }));
  
      setNodes(newNodes);
      setEdges(newEdges);
  
      setTimeout(() => fitView({ padding: 0.25 }), 50);
    };
  
    window.addEventListener("loadWorkflowGraph", handler);
    return () => window.removeEventListener("loadWorkflowGraph", handler);
  }, [setNodes, setEdges, fitView]);  

  useEffect(() => {
    const refreshAgents = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const userId = session?.user?.id || localStorage.getItem("anon_user_id") || "anonymous";
  
      const { data } = await supabase
        .from("agents")
        .select("*")
        .eq("owner_id", userId)
        .order("created_at", { ascending: false });
  
      setCustomAgents(
        (data || []).map(a => ({
          uiLabel: a.agent_name,
          backendLabel: a.agent_name,
          desc: a.description || "",
        }))
      );
    };
  
    window.addEventListener("refreshAgents", refreshAgents);
    return () => window.removeEventListener("refreshAgents", refreshAgents);
  }, []);
  
  // 🔹 Auto-load latest custom workflow after save/generate
  useEffect(() => {
    const onSaved = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const userId = session?.user?.id;
      if (!userId) return;
      
      const { data } = await supabase
        .from("workflows")
        .select("name")
        .eq("user_id", userId)
        .order("created_at", { ascending: false })
        .limit(1)
        .maybeSingle();

      if (data?.name) {
        await loadWorkflowFromDB(data.name);
      }
    };

    window.addEventListener("workflow-saved", onSaved);
    return () => window.removeEventListener("workflow-saved", onSaved);
  }, [supabase]);


  useEffect(() => {
    function handleLoadWorkflowGraph(e: any) {
      const wf = e.detail;
      if (!wf) return;
      setNodes(wf.nodes || []);
      setEdges(wf.edges || []);
    }
  
    window.addEventListener("loadWorkflowGraph", handleLoadWorkflowGraph);
    return () =>
      window.removeEventListener("loadWorkflowGraph", handleLoadWorkflowGraph);
  }, []);


  /* ---------- Default Verify Loop ---------- */
  useEffect(() => {
    const n: Node<AgentNodeData>[] = [
      { id: "spec", type: "agentNode", position: { x: 60, y: 180 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
      { id: "rtl", type: "agentNode", position: { x: 300, y: 180 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
      { id: "tb", type: "agentNode", position: { x: 540, y: 180 }, data: { uiLabel: "Verification Agent", backendLabel: "Digital Testbench Agent" } },
      { id: "sim", type: "agentNode", position: { x: 780, y: 180 }, data: { uiLabel: "Sim Agent", backendLabel: "Digital Sim Agent" } },
    ];
    const e: Edge[] = [
      { id: "e-spec-rtl", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      { id: "e-rtl-tb", source: "rtl", target: "tb", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      { id: "e-tb-sim", source: "tb", target: "sim", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
    ];
    setNodes(n);
    setEdges(e);
  }, []);

  /* ---------- Drag & Drop ---------- */
  const onDragStartAgent = (ev: React.DragEvent, item: CatalogItem) => {
    ev.dataTransfer.setData("application/reactflow", JSON.stringify(item));
    ev.dataTransfer.effectAllowed = "move";
  };

  const onDragOverCanvas = (ev: React.DragEvent) => {
    ev.preventDefault();
    ev.dataTransfer.dropEffect = "move";
  };

  const onDropCanvas = useCallback(
    async (ev: React.DragEvent) => {
      ev.preventDefault();
      const raw = ev.dataTransfer.getData("application/reactflow");
      if (!raw) return;
      const agent: CatalogItem = JSON.parse(raw);

      const bounds = (ev.currentTarget as HTMLDivElement).getBoundingClientRect();
      const position = rf.project({ x: ev.clientX - bounds.left, y: ev.clientY - bounds.top });

      const id = `${agent.uiLabel}-${Date.now()}`;
      const newNode: Node<AgentNodeData> = {
        id,
        type: "agentNode",
        position,
        data: { uiLabel: agent.uiLabel, backendLabel: agent.backendLabel, desc: agent.desc },
      };

      setNodes((nds) => nds.concat(newNode));

      try {
        const res = await fetch(`${API_BASE}/suggest_next_agent`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ outputs: [agent.backendLabel], domain: loop })
        });
        const j = await res.json();
        console.log("Suggested connection:", j);
      } catch (e) {
        console.warn("Suggestion failed", e);
      }
      setEdges((eds) => {
        if (nodes.length === 0) return eds;
        const lastNode = getRightMostNode(nodes);
        if (!lastNode) return eds;
        const newEdge: Edge = {
          id: `e-${lastNode.id}-${id}`,
          source: lastNode.id,
          target: id,
          animated: true,
          style: { stroke: "#22d3ee", strokeWidth: 2 },
        };
        return eds.concat(newEdge);
      });
    },
    [rf, nodes, setNodes, setEdges]
  );

  const getRightMostNode = (nds: Node[]) => {
    if (!nds.length) return null;
    return nds.reduce((acc, n) => (n.position.x > acc.position.x ? n : acc), nds[0]);
  };

  const onConnect = useCallback(
    (params: Connection | Edge) => setEdges((eds) => addEdge({ ...params, animated: true, style: { stroke: "#22d3ee" } }, eds)),
    [setEdges]
  );

  /* ---------- Actions ---------- */
  const runWorkflow = async () => {
    const { data, error } = await supabase
      .from("workflows")
      .insert([{ name: "Verify Loop", status: "running", logs: "🚀 Started verify loop...\n" }])
      .select("id")
      .single();

    if (error || !data?.id) return;
    setJobId(data.id as string);
    setActiveTab("live");
  };

  const saveWorkflowLocal = () => {
    localStorage.setItem("workflow_verify_loop", JSON.stringify({ loop, nodes, edges }));
  };

  const clearWorkflow = () => {
    setNodes([]);
    setEdges([]);
  };

  /* ---------- Derived ---------- */
  const prebuiltAgents = useMemo(() => LOOP_AGENTS[loop], [loop]);

  const prebuiltWorkflows = useMemo(() => {
    const all = {
      digital: ["Verify_Loop", "Spec2RTL"],
      analog: ["Spec2Circuit", "Spec2Sim"],
      embedded: ["Spec2Code", "Spec2Sim"],
      system: ["Digital_IP_Prototype_Loop"]
    };
    return all[loop];
  }, [loop]);

  const loadPrebuiltWorkflow = (wf: string) => {
    // clear existing canvas
    setNodes([]);
    setEdges([]);
  
    if (loop === "digital" && wf.includes("Spec2RTL")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
        { id: "rtl",  type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
      ];
      const e: Edge[] = [
        { id: "e-spec-rtl", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
      setNodes(n);
      setEdges(e);
      setShowSpecModal(true);
    }
    if (loop === "analog" && wf.includes("Spec2Circuit")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Analog Spec Agent" } },
        { id: "netlist", type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "Netlist Agent", backendLabel: "Analog Netlist Agent" } },
      ];
      const e: Edge[] = [
        { id: "e-spec-netlist", source: "spec", target: "netlist", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
      setNodes(n);
      setEdges(e);
      setShowSpecModal(true);
    }
    if (loop === "embedded" && wf.includes("Spec2Code")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 100, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Embedded Spec Agent" } },
        { id: "code", type: "agentNode", position: { x: 360, y: 200 }, data: { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent" } },
      ];
      const e: Edge[] = [{ id: "e-spec-code", source: "spec", target: "code", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } }];
      setNodes(n);
      setEdges(e);
      setShowSpecModal(true);
    }
    if (loop === "system" && wf.includes("Digital_IP_Prototype_Loop")) {
      const n: Node<AgentNodeData>[] = [
        { id: "spec", type: "agentNode", position: { x: 80, y: 200 }, data: { uiLabel: "Spec Agent", backendLabel: "Digital Spec Agent" } },
        { id: "rtl", type: "agentNode", position: { x: 300, y: 200 }, data: { uiLabel: "RTL Agent", backendLabel: "Digital RTL Agent" } },
        { id: "code", type: "agentNode", position: { x: 520, y: 200 }, data: { uiLabel: "Firmware Agent", backendLabel: "Embedded Code Agent" } },
        { id: "sim", type: "agentNode", position: { x: 740, y: 200 }, data: { uiLabel: "Sim Agent", backendLabel: "Embedded Sim Agent" } },
        { id: "result", type: "agentNode", position: { x: 960, y: 200 }, data: { uiLabel: "Result Agent", backendLabel: "Embedded Result Agent" } },
      ];
    
      const e: Edge[] = [
        { id: "e1", source: "spec", target: "rtl", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e2", source: "rtl", target: "code", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e3", source: "code", target: "sim", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
        { id: "e4", source: "sim", target: "result", animated: true, style: { stroke: "#22d3ee", strokeWidth: 2 } },
      ];
    
      setNodes(n);
      setEdges(e);
      setShowSpecModal(true);
    }
  };

  const loadCustomWorkflow = (wfName: string) => {
    const stored = localStorage.getItem(`workflow_${wfName}`);
    if (!stored) return;
    const { nodes, edges } = JSON.parse(stored);
    setNodes(nodes);
    setEdges(edges);
    fitView({ padding: 0.2 });
  };

  const loadCustomWorkflowsFromDB = async () => {

    const userId = await getStableUserId(supabase);
    console.log("🧠 (CustomWork) Loading workflows for:", userId);

    const { data, error } = await supabase
      .from("workflows")
      .select("name, created_at")
      .eq("user_id", userId)        // ✅ Correct filtering
      .order("created_at", { ascending: false });

    if (error) {
      console.error("❌ Error loading workflows:", error);
      return;
    }
   
    // 1) Read local first (for fallback)
    //const localNames = Object.keys(localStorage)
     // .filter((k) => k.startsWith("workflow_"))
    //  .map((k) => k.replace("workflow_", ""));
  
    // 2) Build DB query: include both anonId and NULL
    //let q = supabase
    //  .from("workflows")
     // .select("id, name, created_at, user_id")
     // .order("created_at", { ascending: false });
    
    //if (userId && userId !== "undefined" && userId !== "anonymous") {
    // q = q.or(`user_id.eq.${userId},user_id.is.null`);
    //} else {
    //   q = q.or(`user_id.is.null`);
    //}  

    //const { data, error } = await q;
    //if (error) {
     // console.error("❌ Error loading workflows:", error);
      // fallback to local only
     // setCustomWorkflows([...new Set(localNames)]);
     // return;
    //}
  
    //const dbNames = (data || []).map((wf) => wf.name || `workflow_${wf.id}`);

    const dbNames = (data || []).map(w => w.name);

    console.log("📁 Loaded workflows:", dbNames);
    setCustomWorkflows(dbNames);
  
    // 3) Union (DB ⊎ local), DB first
    //const union = Array.from(new Set([...dbNames, ...localNames]));
    //console.log("📁 Loaded workflows:", union);
    //setCustomWorkflows(union);
  };
  const loadWorkflowFromDB = async (wfName: string) => {
    try {
      // 1) Get user ID (session → anon → fail)
      const userId = await getStableUserId(supabase);  // ✅ unified identity

      console.log(`🧠 Loading workflow: ${wfName} for user: ${userId}`);
 
      if (!userId) {
        console.warn("⚠️ No user ID detected.");
        return;
      }
  

  
      // 2) Fetch workflow record
      const { data, error } = await supabase
        .from("workflows")
        .select("definitions")
        .eq("user_id", userId)
        .eq("name", wfName)
        .maybeSingle();
  
      console.log("📦 Returned from Supabase:", data);
  
      if (error) {
        console.error("❌ Supabase fetch error:", error.message);
        return;
      }
      if (!data || !data.definitions) {
        console.warn("⚠️ No definitions found for:", wfName);
        return;
      }
  
      const defs = data.definitions;
      const nodes = defs.nodes || [];
      const edges = defs.edges || [];
  
      // 3) Normalize nodes for ReactFlow rendering
      const parsedNodes = (defs.nodes || []).map((n: any, i: number) => ({
        id: n.id || `n${i}`,
        type: "agentNode", // <----- IMPORTANT!!!
        position: n.position || { x: 100 + i * 220, y: 200 },
        data: {
          uiLabel: n.data?.uiLabel || n.data?.label || n.data?.backendLabel || "Agent",
          backendLabel: n.data?.backendLabel || n.data?.uiLabel || "Unknown Agent",
          desc: n.data?.desc || "",
        },
      }));
  
      // 4) Normalize edges
      const parsedEdges = (defs.edges || []).map((e: any, i: number) => ({
        id: e.id || `e${i}`,
        source: e.source || e.from,
        target: e.target || e.to,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      }));
  
      console.log(`✅ Parsed ${parsedNodes.length} nodes & ${parsedEdges.length} edges`);
  
      // 5) Update canvas
      setNodes(parsedNodes);
      setEdges(parsedEdges);
  
      setTimeout(() => {
        fitView({ padding: 0.25, duration: 600 });
        console.log("🎨 fitView executed — workflow rendered");
      }, 50);
  
    } catch (err) {
      console.error("🔥 Unexpected load error:", err);
    }
  };
  
  
  

  const handleSpecSubmit = async (text: string, file?: File) => {
    try {
      // Determine which loop is active
      let workflow: any = {};
  
      if (loop === "digital") {
        workflow = {
          loop_type: "digital",
          nodes: [
            { label: "Digital Spec Agent" },
            { label: "Digital RTL Agent" },
          ],
        };
      } else if (loop === "analog") {
        workflow = {
          loop_type: "analog",
          nodes: [
            { label: "Analog Spec Agent" },
            { label: "Analog Netlist Agent" },
          ],
        };
      } else if (loop === "embedded") {
        workflow = {
          loop_type: "embedded",
          nodes: [
            { label: "Embedded Spec Agent" },
            { label: "Embedded Code Agent" },
          ],
        };
      } else if (loop === "system") {
        workflow = {
          loop_type: "system",
          nodes: [
            { label: "Digital Spec Agent" },
            { label: "Digital RTL Agent" },
            { label: "Embedded Code Agent" },
            { label: "Embedded Sim Agent" },
            { label: "Embedded Result Agent" },
          ],
        };
      }
  
      // Build form data for /run_workflow
      const formData = new FormData();
      formData.append("workflow", JSON.stringify(workflow));
      formData.append("spec_text", text || "");
      if (file) formData.append("file", file);
  
      // Hit the unified backend route
      const res = await fetch(`${API_BASE}/run_workflow`, {
        method: "POST",
        body: formData,
      });
  
      const result = await res.json();
  
      if (result.status === "success" || result.workflow_id) {
        console.log(`✅ ${loop} workflow started:`, result.workflow_id);
        setJobId(result.workflow_id);
        setActiveTab("live");
      } else {
        console.error("❌ Backend error:", result.message || result.error);
      }
    } catch (err) {
      console.error("❌ API call failed:", err);
    }
  };
  

  
  

  /* =========================
     Render
  ========================= */
  return (
    <main className="h-screen overflow-hidden bg-[#0b0b0c] text-white flex flex-col">
      {/* ===== Top bar ===== */}
      <nav className="w-full flex justify-between items-center px-6 py-4 bg-black/70 backdrop-blur border-b border-slate-800">
        <div
          onClick={() => router.push("/")}
          className="text-2xl font-extrabold text-cyan-400 cursor-pointer"
        >
          CHIPLOOP ⚡
        </div>
        <div className="flex items-center gap-6 text-slate-300">
          <button onClick={() => router.push("/")} className="hover:text-cyan-400 transition">
            Home
          </button>
          <button onClick={() => router.push("/pricing")} className="hover:text-cyan-400 transition">
            Pricing
          </button>
          <button
            onClick={async () => {
              await supabase.auth.signOut();
              router.push("/");
            }}
            className="rounded-lg bg-slate-800 px-4 py-2 hover:bg-slate-700"
          >
            Logout
          </button>
        </div>
      </nav>
  
      <div className="flex flex-1 overflow-hidden">
        {/* ===== Sidebar ===== */}
        <aside className="w-72 bg-slate-900/70 border-r border-slate-800 p-4 flex flex-col overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          {/* 🧠 Agentic Tools */}
          <h2 className="text-lg font-bold mb-3 text-cyan-400">Agentic Tools</h2>
          <button
            onClick={() => setShowPlanner(true)}
            className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-600 hover:bg-cyan-500 text-white"
          >
            Workflow Builder
          </button>
          <button
            onClick={() => setShowAgentPlanner(true)}
            className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-600 hover:bg-cyan-500 text-white"
          >
            Agent Planner
          </button>
          <div className="border-t border-slate-800 my-3" />
          {/* 🔁 Loop Selector */}
          <div className="mb-4">
            <label className="block text-xs uppercase text-cyan-400 mb-2">Loop</label>
            <select
              value={loop}
              onChange={(e) => setLoop(e.target.value as LoopKey)}
              className="w-full rounded-lg bg-slate-800 border border-slate-700 p-2 text-slate-200"
            >
              <option value="digital">Digital Loop</option>
              <option value="analog">Analog Loop</option>
              <option value="embedded">Embedded Loop</option>
              <option value="system">System Loop</option>
            </select>
          </div>
  
          {/* ===== Divider before Workflows ===== */}
          <div className="border-t border-slate-800 my-3" />
  
          {/* ⚙️ Workflows */}
          <section className="mb-6">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Workflows</h3>
  
            <div className="pl-2">
              <p className="text-sm text-cyan-400 font-medium mb-1">Prebuilt</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-32 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent mb-3">
                {prebuiltWorkflows.map((wf) => (
                  <li
                    key={wf}
                    onClick={() => loadPrebuiltWorkflow(wf)}
                    className="px-2 py-1 rounded hover:bg-slate-800 cursor-pointer"
                  >
                    {wf}
                  </li>
                ))}
              </ul>
          {customWorkflows && customWorkflows.length > 0 && (
            <>
              <p className="text-sm text-cyan-400 font-medium mb-1">Custom</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-60 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
               {customWorkflows.map((wf, idx) => (
                  <li
                    key={`${wf}-${idx}`}
                    onClick={() => loadWorkflowFromDB(wf)}
                    onContextMenu={(e) => openContextMenu(e, wf)}
                    className= "px-2 py-1 rounded hover:bg-slate-800 cursor-pointer select-none"
                  >
                    {wf}
                  </li>
                ))}
              </ul>
            </>
          )}
           
            </div>
          </section>
  
          {/* ===== Divider before Agents ===== */}
          <div className="border-t border-slate-800 my-3" />
  
          {/* 🤖 Agents */}
          <section className="mb-6">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Agents</h3>
  
            <div className="pl-2">
              <p className="text-sm text-cyan-400 font-medium mb-1">Prebuilt</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-32 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent mb-3">
                {prebuiltAgents.map((a) => (
                  <li
                    key={a.backendLabel}
                    draggable
                    onDragStart={(e) => onDragStartAgent(e, a)}
                    className="cursor-grab active:cursor-grabbing px-2 py-1 rounded hover:bg-slate-800"
                    title={`${a.uiLabel} — ${a.desc || ""}`}
                  >
                    {a.uiLabel}
                  </li>
                ))}
              </ul>
  
              <p className="text-sm text-cyan-400 font-medium mb-1">Custom</p>
              <ul className="space-y-1 text-sm text-gray-300 overflow-y-auto max-h-60 pr-1 pl-3 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
                {customAgents.length ? (
                  customAgents.map((a, idx) => (
                    <li
                      key={`${a.backendLabel}-${idx}`}
                      draggable
                      onDragStart={(e) => onDragStartAgent(e, a)}
                      onContextMenu={(e) => openAgentMenu(e, a.backendLabel)}
                      className="cursor-grab active:cursor-grabbing px-2 py-1 rounded hover:bg-slate-800"
                    >
                      {a.uiLabel}
                    </li>
                  ))
                ) : (
                  <p className="text-xs text-slate-400">No custom agents yet</p>
                )}
              </ul>
            </div>
          </section>
  
          {/* 🛍 Marketplace */}
          <div className="mt-auto border-t border-slate-700 pt-3">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Marketplace</h3>
  
            <button
              onClick={() => setShowSubmitMarketplaceModal(true)}
              className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-500 hover:bg-cyan-400 text-white"
            >
              Submit for Review
            </button>
  
            <button
              onClick={() => router.push("/marketplace")}
              className="w-full text-left px-3 py-2 mb-1 rounded bg-cyan-500 hover:bg-cyan-400 text-white"
            >
              View Public Marketplace
            </button>
          </div>
        </aside>
  
        {/* ===== Canvas & Console ===== */}
        <section className="flex-1 flex flex-col p-4 overflow-hidden">
          {/* Canvas */}
          <div
            className="relative flex-1 border border-slate-800 rounded-xl overflow-hidden bg-black/60"
            onDrop={onDropCanvas}
            onDragOver={onDragOverCanvas}
          >
            <ReactFlow
              key={nodes.map(n => n.id).join("-")}
              nodes={nodes}
              edges={edges}
              onNodesChange={onNodesChange}
              onEdgesChange={onEdgesChange}
              onConnect={onConnect}
              nodeTypes={{ agentNode: AgentNode }}
              fitView
              defaultEdgeOptions={{ animated: true, style: { stroke: '#22d3ee' } }}
            >
             
              <Controls />
              <Background color="#334155" gap={20} />
            </ReactFlow>
          </div>
  
          {/* Action Buttons */}
          <div className="flex justify-center gap-4 py-4 border-t border-slate-800 bg-black/40 mt-4">
            <button 
              className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400"
              onClick={() => {
                setNodes([]);
                setEdges([]);
              }}
            >
              New Workflow
            </button>
            <button onClick={runWorkflow} className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400">
              Run Workflow
            </button>
            <button
              onClick={async () => {
                const workflowName = prompt("💾 Enter a name for this workflow:", `CanvasFlow_${new Date().toISOString().slice(0, 10)}`);


                //const { data: sessionData } = await supabase.auth.getSession();
                //const anonId = localStorage.getItem("anon_user_id");
                //const userId = sessionData?.session?.user?.id || anonId || "anonymous";

                const userId = await getStableUserId();
            
                await fetch("/api/save_custom_workflow", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify({
                    user_id: userId,
                    name: workflowName.trim(),
                    goal: "",
                    summary: `Workflow created from canvas: ${workflowName}`,
                    loop_type: loop.toLowerCase(),   // ✅ correct loop
                    definitions: { nodes, edges },   // ✅ actual workflow graph!
                    status: "saved",
                  }),
                });
            
                window.dispatchEvent(new Event("refreshWorkflows"));
                alert(`✅ Workflow "${workflowName}" saved successfully.`);
              }}
              className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400"
            >
              Save Workflow
            </button>
            <button onClick={clearWorkflow} className="rounded-lg bg-cyan-500 px-4 py-2 font-bold text-black hover:bg-cyan-400">
              Clear
            </button>
          </div>
  
          {/* Workflow Execution Tabs */}
          <div className="border-t border-slate-800 bg-black/70 p-4 mt-2 rounded-md overflow-y-auto scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
            <h3 className="mb-2 text-cyan-400 font-semibold">⚡ Workflow Run updates </h3>
  
            <div className="flex gap-4 border-b border-slate-800 mb-4">
              <button
                onClick={() => setActiveTab("summary")}
                className={`pb-2 ${activeTab === "summary" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Summary
              </button>
              <button
                onClick={() => setActiveTab("live")}
                className={`pb-2 ${activeTab === "live" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Live Feed
              </button>
              <button
                onClick={() => setActiveTab("output")}
                className={`pb-2 ${activeTab === "output" ? "text-cyan-400 border-b-2 border-cyan-400" : "text-slate-400"}`}
              >
                Output Logs
              </button>
            </div>
  
            <div
              className={`rounded-lg border p-3 transition-all duration-300 ${
                activeTab === "summary" || activeTab === "live" || activeTab === "output"
                  ? "border-cyan-500/60 shadow-[0_0_8px_rgba(34,211,238,0.3)]"
                  : "border-slate-700"
              }`}
            >
              {activeTab === "live" && jobId && <WorkflowConsole jobId={jobId} table="workflows" />}
              {activeTab === "summary" && <div></div>}
              {activeTab === "output" && <div></div>}
            </div>
          </div>
        </section>
      </div>

      {contextMenu && (
        <div
          onMouseLeave={closeContextMenu}
          style={{ top: contextMenu.y, left: contextMenu.x }}
          className="fixed z-50 bg-slate-800 border border-slate-700 rounded-md shadow-lg"
        >
          <button
            onClick={() => setRenameTarget({ oldName: contextMenu.name, newName: "" })}
            className="block w-full text-left px-3 py-2 text-sky-300 hover:bg-slate-700"
          >
           ✏️ Rename “{contextMenu.name}”
          </button>
          <button
            onClick={() => deleteCustomWorkflow(contextMenu.name)}
            className="block w-full text-left px-3 py-2 text-red-400 hover:bg-slate-700"
          >
            🗑 Delete “{contextMenu.name}”
          </button>
        </div>
      )}

      {renameTarget.oldName && (
        <div className="fixed inset-0 bg-black/60 z-50 flex items-center justify-center">
          <div className="bg-slate-900 rounded-xl p-6 shadow-xl w-96">
            <h3 className="text-lg font-bold mb-3 text-cyan-400">Rename Workflow</h3>
            <p className="text-sm mb-2 text-slate-400">Old name: {renameTarget.oldName}</p>
            <input
              type="text"
              value={renameTarget.newName}
              onChange={(e) => setRenameTarget({ ...renameTarget, newName: e.target.value })}
              placeholder="Enter new name"
              className="w-full mb-4 rounded-lg bg-slate-800 border border-slate-700 p-2 text-slate-200"
            />
           <div className="flex justify-end gap-2">
              <button
                onClick={() => setRenameTarget({ oldName: "", newName: "" })}
                className="px-4 py-2 rounded bg-slate-700 hover:bg-slate-600"
              >
                Cancel
              </button>
              <button
                onClick={renameCustomWorkflow}
                className="px-4 py-2 rounded bg-cyan-500 text-black font-semibold hover:bg-cyan-400"
              >
                Rename
              </button>
            </div>
          </div>
        </div>
      )}

             {/* Agent context menu */}
      {agentMenu && (
          <div
            className="fixed z-50 bg-slate-800 text-white border border-slate-600 rounded shadow-xl py-1"
            style={{ left: agentMenu.x, top: agentMenu.y }}
            onMouseLeave={closeAgentMenu}
          >
            <button
              className="px-4 py-1 hover:bg-slate-700 w-full text-left"
              onClick={() => renameCustomAgent(agentMenu.name)}
            >
              ✏️ Rename
            </button>
            <button
              className="px-4 py-1 hover:bg-slate-700 w-full text-left text-red-400"
              onClick={() => deleteCustomAgent(agentMenu.name)}
            >
              🗑 Delete
            </button>
          </div>
      )}
  
      {/* ===== Modals ===== */}
      {showSpecModal && (
        <SpecInputModal
          loop={loop}
          onClose={() => setShowSpecModal(false)}
          onSubmit={(text, file) => {
            handleSpecSubmit(text, file);
            setShowSpecModal(false);
            console.log("Spec submitted:", { text, file });
          }}
        />
      )}
  
      {showCreateAgentModal && (
        <CreateAgentModal
          onClose={() => setShowCreateAgentModal(false)}
          onSubmit={(backendLabel, uiLabel, desc) => {
            const next = [...customAgents, { uiLabel, backendLabel, desc }];
            setCustomAgents(next);
            localStorage.setItem("custom_agents", JSON.stringify(next));
          }}
        />
      )}
  
      {showPlanner && <PlannerModal onClose={() => setShowPlanner(false)} />}
      {showAgentPlanner && <AgentPlannerModal onClose={() => setShowAgentPlanner(false)} />}
    </main>
  );
  
  
}

/* =========================
   Modals (unchanged)
========================= */
function SpecInputModal({ loop, onClose, onSubmit }: { loop: string; onClose: () => void; onSubmit: (text: string, file?: File) => void }) {
  const [text, setText] = useState("");
  const [file, setFile] = useState<File | null>(null);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-2xl rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
      <h2 className="mb-4 text-2xl font-bold text-cyan-400">Enter Spec for {loop.charAt(0).toUpperCase() + loop.slice(1)} Loop</h2>
        <textarea
          className="mb-4 h-40 w-full rounded-lg border border-slate-600 bg-slate-800 p-4 text-lg outline-none focus:ring-2 focus:ring-cyan-500"
          placeholder={
              loop === "digital"
              ? "Describe the digital module (I/Os, behavior)"
              : loop === "analog"
              ? "Describe the analog circuit (R, C, gain, etc.)"
              : loop === "embedded"
              ? "Describe MCU logic and IO behavior"
              : "Describe System (integrated digital + firmware+Analog) behavior"
          }
          value={text}
          onChange={(e) => setText(e.target.value)}
        />
        <div className="mb-4">
          <label className="mb-2 block text-sm font-medium">Upload Spec Document</label>
          <label htmlFor="file-upload" className="flex w-full cursor-pointer items-center justify-center rounded-lg border-2 border-dashed border-slate-600 bg-slate-800 px-4 py-6 hover:bg-slate-700">
            <svg xmlns="http://www.w3.org/2000/svg" className="mr-2 h-6 w-6 text-cyan-400" fill="none" viewBox="0 0 24 24" stroke="currentColor" strokeWidth={2}>
              <path strokeLinecap="round" strokeLinejoin="round" d="M4 16v1a2 2 0 002 2h12a2 2 0 002-2v-1M12 12V4m0 8l-3-3m3 3l3-3" />
            </svg>
            <span className="text-slate-300">Click to upload</span>
            <input id="file-upload" type="file" accept=".txt,md,pdf" className="hidden" onChange={(e) => setFile(e.target.files?.[0] || null)} />
          </label>
          {file && <p className="mt-2 text-sm text-green-400">📄 {file.name} selected</p>}
        </div>
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">Cancel</button>
          <button
            onClick={() => { onSubmit(text, file || undefined); onClose(); }}
            className="rounded-lg bg-cyan-500 px-6 py-2 font-bold text-black hover:bg-cyan-400"
          >
            Run Spec Agent
          </button>
        </div>
      </div>
    </div>
  );
}

function CreateAgentModal({ onClose, onSubmit }: { onClose: () => void; onSubmit: (backendLabel: string, uiLabel: string, desc: string) => void }) {
  const [backendKey, setBackendKey] = useState("");
  const [uiLabel, setUiLabel] = useState("");
  const [desc, setDesc] = useState("");

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70">
      <div className="w-full max-w-lg rounded-2xl bg-slate-900 p-6 text-slate-100 shadow-2xl">
        <h2 className="mb-4 text-2xl font-bold text-cyan-400">Create Custom Agent</h2>
        <input type="text" placeholder='Backend label (e.g. "Digital RTL Agent")' value={backendKey} onChange={(e) => setBackendKey(e.target.value)} className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <input type="text" placeholder='UI label (e.g. "RTL Agent")' value={uiLabel} onChange={(e) => setUiLabel(e.target.value)} className="mb-3 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <textarea placeholder="Describe what this agent does." value={desc} onChange={(e) => setDesc(e.target.value)} className="mb-4 h-28 w-full rounded border border-slate-600 bg-slate-800 p-2" />
        <div className="flex justify-end space-x-3">
          <button onClick={onClose} className="rounded-lg bg-slate-700 px-4 py-2 hover:bg-slate-600">Cancel</button>
          <button onClick={() => { onSubmit(backendKey, uiLabel || backendKey, desc); onClose(); }} className="rounded-lg bg-emerald-500 px-6 py-2 font-bold text-black hover:bg-emerald-400">
            Save Agent
          </button>
        </div>
      </div>
    </div>
  );
}
