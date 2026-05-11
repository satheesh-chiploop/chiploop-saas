"use client";

import { useEffect, useMemo, useState } from "react";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import type { Edge, Node } from "reactflow";
import { ApiClientError, apiPost } from "@/lib/apiClient";
import { getStableUserId } from "@/utils/userId";

type SavedWorkflowOption = {
  id?: string;
  name: string;
  displayName?: string;
  loop_type?: string | null;
  is_prebuilt?: boolean | null;
  definitions?: { nodes?: Node[]; edges?: Edge[] } | null;
};

type DagPreviewModalProps = {
  loopType: string;
  nodes: Node[];
  edges: Edge[];
  savedWorkflows?: SavedWorkflowOption[];
  selectedWorkflowName?: string | null;
  onOpenComposedWorkflow?: (workflow: { nodes: Node[]; edges: Edge[]; name?: string; loopType?: string }) => void;
  onClose: () => void;
};

type DagPreviewResponse = {
  status: string;
  valid?: boolean;
  warnings?: string[];
  errors?: string[];
  dag?: {
    nodes?: unknown[];
    edges?: unknown[];
  };
  preview?: {
    execution_order?: string[];
    parallel_groups?: string[][];
    dependency_graph?: Record<string, { agent_name?: string; depends_on?: string[]; can_run_parallel?: boolean }>;
    parallel_group_agents?: string[][];
  };
};

type DagValidateResponse = {
  status: string;
  valid: boolean;
  errors?: string[];
  warnings?: string[];
};

type SavedWorkflowRecord = {
  id?: string;
  name?: string;
  definitions?: { nodes?: Node[]; edges?: Edge[] } | null;
  loop_type?: string | null;
  is_prebuilt?: boolean | null;
  status?: string | null;
};

type ComposedWorkflow = {
  nodes: Node[];
  edges: Edge[];
  loopType: string;
  sourceNames: string[];
  originalStepCount: number;
  originalSerialSteps: Array<{ agentName: string; sources: string[]; shared: boolean }>;
  agentSources: Record<string, string[]>;
};

const REGISTERED_AGENT_ALIASES: Record<string, string> = {
  "System Integration Agent": "System Integration Intent Agent",
  "System RTL Agent": "System Top Assembly Agent",
  "System Sim Agent": "System Simulation Control Agent",
  "System Firmware Agent": "System Firmware CoSim Execution Agent",
  "System Assertions Agent": "System Assertions (SVA) Agent",
  "System IP Packaging & Handoff Agent": "System RTL Handoff Package Agent",
};

function normalizeAgentName(name: string): string {
  return REGISTERED_AGENT_ALIASES[name] || name;
}

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Workflow Composer request failed.";
}

function graphPayloadFromNodes(nodes: Node[], edges: Edge[], loopType: string) {
  return {
    graph: {
      nodes: nodes.map((node) => ({
        id: node.id,
        data: {
          uiLabel: normalizeAgentName(String(node.data?.uiLabel || node.data?.backendLabel || node.id)),
          backendLabel: normalizeAgentName(String(node.data?.backendLabel || node.data?.uiLabel || node.id)),
        },
      })),
      edges: edges.map((edge) => ({
        source: edge.source,
        target: edge.target,
      })),
    },
    loop_type: loopType,
  };
}

function inferAgentDomain(node: Node): string {
  const label = String(node.data?.backendLabel || node.data?.uiLabel || node.id).toLowerCase();
  if (label.includes("analog")) return "analog";
  if (label.includes("embedded") || label.includes("firmware")) return "embedded";
  if (label.includes("validation")) return "validation";
  if (label.includes("system")) return "system";
  if (label.includes("digital") || label.includes("rtl") || label.includes("synthesis") || label.includes("floorplan")) return "digital";
  return "other";
}

function isSystemJoinCandidate(node: Node): boolean {
  const label = String(node.data?.backendLabel || node.data?.uiLabel || node.id).toLowerCase();
  return (
    label.includes("system top assembly") ||
    label.includes("system integration") ||
    label.includes("system testbench") ||
    label.includes("system simulation")
  );
}

function sortedNodes(nodes: Node[]): Node[] {
  return [...nodes].sort((a, b) => {
    const ax = Number(a.position?.x || 0);
    const bx = Number(b.position?.x || 0);
    if (ax !== bx) return ax - bx;
    return Number(a.position?.y || 0) - Number(b.position?.y || 0);
  });
}

function workflowSerialNodes(nodes: Node[], edges?: Edge[]): Node[] {
  if (!edges?.length) return nodes;
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const indegree = new Map(nodes.map((node) => [node.id, 0]));
  const outgoing = new Map<string, string[]>();
  edges.forEach((edge) => {
    if (!nodeById.has(edge.source) || !nodeById.has(edge.target)) return;
    outgoing.set(edge.source, [...(outgoing.get(edge.source) || []), edge.target]);
    indegree.set(edge.target, (indegree.get(edge.target) || 0) + 1);
  });

  const originalIndex = new Map(nodes.map((node, index) => [node.id, index]));
  const queue = nodes
    .filter((node) => (indegree.get(node.id) || 0) === 0)
    .sort((a, b) => (originalIndex.get(a.id) || 0) - (originalIndex.get(b.id) || 0));
  const ordered: Node[] = [];

  while (queue.length) {
    const node = queue.shift();
    if (!node) break;
    ordered.push(node);
    (outgoing.get(node.id) || []).forEach((targetId) => {
      indegree.set(targetId, (indegree.get(targetId) || 0) - 1);
      if ((indegree.get(targetId) || 0) === 0) {
        const targetNode = nodeById.get(targetId);
        if (targetNode) {
          queue.push(targetNode);
          queue.sort((a, b) => (originalIndex.get(a.id) || 0) - (originalIndex.get(b.id) || 0));
        }
      }
    });
  }

  return ordered.length === nodes.length ? ordered : nodes;
}

function agentLabelFromNode(node: Node): string {
  return normalizeAgentName(String(node.data?.backendLabel || node.data?.uiLabel || node.id));
}

function uniqueStrings(values: string[]): string[] {
  return Array.from(new Set(values.filter(Boolean)));
}

function suggestBranchWorkflowFromCurrent(nodes: Node[], loopType: string, sourceName = "Current workflow", originalEdges?: Edge[]): ComposedWorkflow {
  const rowByDomain: Record<string, number> = {
    digital: 110,
    analog: 290,
    embedded: 470,
    validation: 650,
    other: 830,
  };
  const clonedNodes = nodes.map((node) => ({
    ...node,
    type: node.type || "agentNode",
    data: {
      uiLabel: String(node.data?.uiLabel || node.data?.backendLabel || node.id),
      backendLabel: agentLabelFromNode(node),
      desc: node.data?.desc,
    },
  }));
  const agentSources = Object.fromEntries(clonedNodes.map((node) => [node.id, [sourceName]]));
  const groups = new Map<string, Node[]>();
  clonedNodes.forEach((node) => {
    const domain = inferAgentDomain(node);
    groups.set(domain, [...(groups.get(domain) || []), node]);
  });

  const systemNodes = sortedNodes(groups.get("system") || []);
  let branchMaxX = 80;
  for (const [domain, domainNodes] of groups.entries()) {
    if (domain === "system" || !domainNodes.length) continue;
    const ordered = sortedNodes(domainNodes);
    const rowY = rowByDomain[domain] ?? rowByDomain.other;
    ordered.forEach((node, index) => {
      node.position = { x: 80 + index * 260, y: rowY };
      branchMaxX = Math.max(branchMaxX, node.position.x);
    });
  }
  systemNodes.forEach((node, index) => {
    node.position = { x: branchMaxX + 300 + index * 260, y: 370 };
  });

  const joinNode = systemNodes.find(isSystemJoinCandidate) || systemNodes[0];
  const composedEdges: Edge[] = [];

  for (const [domain, domainNodes] of groups.entries()) {
    if (domain === "system" || !domainNodes.length) continue;
    const ordered = sortedNodes(domainNodes);
    ordered.slice(1).forEach((node, index) => {
      const previous = ordered[index];
      composedEdges.push({
        id: `e-suggest-${previous.id}-${node.id}`,
        source: previous.id,
        target: node.id,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      });
    });
    const terminal = ordered[ordered.length - 1];
    if (joinNode && terminal.id !== joinNode.id) {
      composedEdges.push({
        id: `e-suggest-${terminal.id}-${joinNode.id}`,
        source: terminal.id,
        target: joinNode.id,
        animated: true,
        style: { stroke: "#f59e0b", strokeWidth: 2 },
      });
    }
  }

  if (systemNodes.length) {
    const systemStartIndex = joinNode ? systemNodes.findIndex((node) => node.id === joinNode.id) : 0;
    const orderedSystem = systemNodes.slice(Math.max(0, systemStartIndex));
    orderedSystem.slice(1).forEach((node, index) => {
      const previous = orderedSystem[index];
      composedEdges.push({
        id: `e-suggest-${previous.id}-${node.id}`,
        source: previous.id,
        target: node.id,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      });
    });
  }

  if (!composedEdges.length) {
    const ordered = sortedNodes(clonedNodes);
    ordered.slice(1).forEach((node, index) => {
      const previous = ordered[index];
      composedEdges.push({
        id: `e-suggest-${previous.id}-${node.id}`,
        source: previous.id,
        target: node.id,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      });
    });
  }

  return {
    nodes: clonedNodes,
    edges: composedEdges,
    loopType,
    sourceNames: [sourceName],
    originalStepCount: nodes.length,
    originalSerialSteps: workflowSerialNodes(nodes, originalEdges).map((node) => ({
      agentName: agentLabelFromNode(node),
      sources: [sourceName],
      shared: false,
    })),
    agentSources,
  };
}

function workflowKey(workflow: SavedWorkflowOption): string {
  return workflow.id || workflow.name;
}

function workflowLabel(workflow: SavedWorkflowOption): string {
  const label = workflow.displayName || workflow.name;
  return workflow.is_prebuilt ? `${label} (Prebuilt)` : label;
}

function composeWorkflowFromDefinitions(
  workflows: Array<{ workflow: SavedWorkflowOption; definitions: { nodes?: Node[]; edges?: Edge[] } }>,
  loopType: string,
  suggestCompositionEdges: boolean,
): ComposedWorkflow {
  const composedNodes: Node[] = [];
  const composedEdges: Edge[] = [];
  const nodeIdByAgentName = new Map<string, string>();
  const remappedNodeIds = new Map<string, string>();
  const edgeKeys = new Set<string>();
  const agentSourceSets: Record<string, Set<string>> = {};
  const originalSerialSteps: Array<{ agentName: string; sources: string[]; shared: boolean }> = [];
  let originalStepCount = 0;
  const branchTerminalIds: string[] = [];
  let joinNodeId = "";

  const addComposedEdge = (edge: Edge) => {
    if (!edge.source || !edge.target || edge.source === edge.target) return;
    const key = `${edge.source}->${edge.target}`;
    if (edgeKeys.has(key)) return;
    edgeKeys.add(key);
    composedEdges.push(edge);
  };

  workflows.forEach(({ workflow, definitions }, workflowIndex) => {
    const prefix = workflowKey(workflow).replace(/[^a-zA-Z0-9_-]/g, "_") || `workflow_${workflowIndex + 1}`;
    const nodes = definitions.nodes || [];
    const edges = definitions.edges || [];
    const orderedWorkflowNodes = workflowSerialNodes(nodes, edges);
    const outgoing = new Set(edges.map((edge) => edge.source));
    const prefixedNodeIds: string[] = [];
    let workflowJoinNodeId = "";
    let workflowHasSystemAgent = false;
    originalStepCount += nodes.length;

    nodes.forEach((node) => {
      const backendLabel = agentLabelFromNode(node);
      const uiLabel = normalizeAgentName(String(node.data?.uiLabel || node.data?.backendLabel || backendLabel));
      const labelLower = backendLabel.toLowerCase();
      const agentKey = backendLabel.toLowerCase();
      const originalNodeKey = `${prefix}__${node.id}`;
      let composedId = nodeIdByAgentName.get(agentKey);

      if (!composedId) {
        composedId = `${prefix}__${node.id}`;
        nodeIdByAgentName.set(agentKey, composedId);
        composedNodes.push({
          id: composedId,
          type: "agentNode",
          position: {
            x: Number(node.position?.x || 80) + workflowIndex * 280,
            y: Number(node.position?.y || 120) + workflowIndex * 160,
          },
          data: {
            uiLabel,
            backendLabel,
          },
        });
      }

      remappedNodeIds.set(originalNodeKey, composedId);
      if (!agentSourceSets[composedId]) agentSourceSets[composedId] = new Set<string>();
      agentSourceSets[composedId].add(workflow.name);
      prefixedNodeIds.push(composedId);
      workflowHasSystemAgent = workflowHasSystemAgent || labelLower.includes("system");
      if (
        !workflowJoinNodeId &&
        (
          labelLower.includes("system top assembly") ||
          labelLower.includes("system integration") ||
          labelLower.includes("system testbench") ||
          labelLower.includes("system simulation")
        )
      ) {
        workflowJoinNodeId = composedId;
      }
    });

    orderedWorkflowNodes.forEach((node) => {
      originalSerialSteps.push({
        agentName: agentLabelFromNode(node),
        sources: [workflow.name],
        shared: false,
      });
    });

    edges.forEach((edge) => {
      const source = remappedNodeIds.get(`${prefix}__${edge.source}`) || `${prefix}__${edge.source}`;
      const target = remappedNodeIds.get(`${prefix}__${edge.target}`) || `${prefix}__${edge.target}`;
      addComposedEdge({
        id: `e-${source}-${target}`,
        source,
        target,
        animated: true,
        style: { stroke: "#22d3ee", strokeWidth: 2 },
      });
    });

    if (workflowHasSystemAgent && !joinNodeId) {
      joinNodeId = workflowJoinNodeId || prefixedNodeIds[0] || "";
    }

    if (!workflowHasSystemAgent) {
      nodes
        .filter((node) => !outgoing.has(node.id))
        .forEach((node) => {
          const remappedId = remappedNodeIds.get(`${prefix}__${node.id}`) || `${prefix}__${node.id}`;
          branchTerminalIds.push(remappedId);
        });
    }
  });

  const agentSources = Object.fromEntries(
    Object.entries(agentSourceSets).map(([nodeId, sources]) => [nodeId, Array.from(sources)]),
  );
  const sourceCountByAgentName = new Map<string, string[]>();
  composedNodes.forEach((node) => {
    const agentName = agentLabelFromNode(node);
    sourceCountByAgentName.set(agentName, agentSources[node.id] || []);
  });

  if (suggestCompositionEdges && workflows.length > 1 && joinNodeId) {
    Array.from(new Set(branchTerminalIds)).forEach((terminalId) => {
      if (terminalId !== joinNodeId) {
        addComposedEdge({
          id: `e-composer-${terminalId}-${joinNodeId}`,
          source: terminalId,
          target: joinNodeId,
          animated: true,
          style: { stroke: "#f59e0b", strokeWidth: 2 },
        });
      }
    });
  }

  return {
    nodes: composedNodes,
    edges: composedEdges,
    loopType,
    sourceNames: workflows.map(({ workflow }) => workflow.name),
    originalStepCount,
    originalSerialSteps: originalSerialSteps.map((step) => {
      const sources = sourceCountByAgentName.get(step.agentName) || step.sources;
      return {
        ...step,
        sources,
        shared: sources.length > 1,
      };
    }),
    agentSources,
  };
}

function graphPayloadFromComposedWorkflow(composed: ComposedWorkflow, suggestCompositionEdges: boolean) {
  return {
    graph: {
      nodes: composed.nodes.map((node) => ({
        id: node.id,
        data: {
          uiLabel: String(node.data?.uiLabel || node.data?.backendLabel || node.id),
          backendLabel: normalizeAgentName(String(node.data?.backendLabel || node.data?.uiLabel || node.id)),
        },
      })),
      edges: composed.edges.map((edge) => ({
        source: edge.source,
        target: edge.target,
      })),
    },
    loop_type: composed.loopType,
    metadata: {
      composer_mode: "saved_workflows",
      suggested_composition_edges: suggestCompositionEdges,
      workflow_names: composed.sourceNames,
    },
  };
}

function samplePayload(loopType: string) {
  return {
    agents: ["Digital Spec Agent", "Digital RTL Agent", "Digital Testbench Generator Agent"],
    loop_type: loopType,
    infer_parallel: true,
  };
}

function parseJson(text: string): unknown {
  try {
    return JSON.parse(text);
  } catch {
    throw new Error("Enter valid workflow JSON before running advanced preview.");
  }
}

function JsonBlock({ title, value }: { title: string; value: unknown }) {
  return (
    <section className="rounded-lg border border-slate-800 bg-black/30 p-3">
      <h4 className="mb-2 text-sm font-bold text-cyan-300">{title}</h4>
      <pre className="max-h-72 overflow-auto whitespace-pre-wrap rounded bg-slate-950 p-3 text-xs text-slate-200">
        {JSON.stringify(value || {}, null, 2)}
      </pre>
    </section>
  );
}

function EmptyState() {
  return (
    <div className="rounded-lg border border-slate-800 bg-black/30 p-5 text-sm text-slate-400">
      Choose a saved or current workflow and click Analyze Parallelism. ChipLoop will show which existing graph stages can run together.
    </div>
  );
}

export default function DagPreviewModal({
  loopType,
  nodes,
  edges,
  savedWorkflows = [],
  selectedWorkflowName,
  onOpenComposedWorkflow,
  onClose,
}: DagPreviewModalProps) {
  const supabase = createClientComponentClient();
  const [source, setSource] = useState<"current" | "saved">("current");
  const [availableSavedWorkflows, setAvailableSavedWorkflows] = useState<SavedWorkflowOption[]>(savedWorkflows);
  const [selectedSavedWorkflowKeys, setSelectedSavedWorkflowKeys] = useState<string[]>(() => {
    const selected = savedWorkflows.find((workflow) => workflow.name === selectedWorkflowName);
    const first = selected || savedWorkflows[0];
    return first ? [workflowKey(first)] : [];
  });
  const [jsonText, setJsonText] = useState(() => JSON.stringify(graphPayloadFromNodes(nodes, edges, loopType), null, 2));
  const [preview, setPreview] = useState<DagPreviewResponse | null>(null);
  const [validation, setValidation] = useState<DagValidateResponse | null>(null);
  const [loading, setLoading] = useState<"preview" | "validate" | "saved" | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [saveStatus, setSaveStatus] = useState<string | null>(null);
  const [advancedOpen, setAdvancedOpen] = useState(false);
  const [suggestCompositionEdges, setSuggestCompositionEdges] = useState(true);
  const [suggestCurrentBranches, setSuggestCurrentBranches] = useState(true);
  const [composedWorkflow, setComposedWorkflow] = useState<ComposedWorkflow | null>(null);

  useEffect(() => {
    setAvailableSavedWorkflows(savedWorkflows);
  }, [savedWorkflows]);

  useEffect(() => {
    if (source !== "saved") return;
    let cancelled = false;

    async function loadWorkflows() {
      setLoading("saved");
      setError(null);
      try {
        const userId = await getStableUserId();
        const [prebuiltResult, customResult] = await Promise.all([
          supabase
            .from("workflows")
            .select("id,name,loop_type,definitions,is_prebuilt,status")
            .eq("is_prebuilt", true)
            .order("name", { ascending: true }),
          supabase
            .from("workflows")
            .select("id,name,loop_type,definitions,is_prebuilt,status")
            .eq("user_id", userId)
            .eq("status", "saved")
            .or("is_prebuilt.eq.false,is_prebuilt.is.null")
            .order("created_at", { ascending: false }),
        ]);

        if (prebuiltResult.error) throw new Error(prebuiltResult.error.message);
        if (customResult.error) throw new Error(customResult.error.message);

        const rows = [...((prebuiltResult.data || []) as SavedWorkflowRecord[]), ...((customResult.data || []) as SavedWorkflowRecord[])];
        const next = rows
          .filter((row) => row.name && row.definitions?.nodes?.length)
          .map((row) => ({
            id: row.id,
            name: String(row.name),
            displayName: String(row.name),
            loop_type: row.loop_type,
            is_prebuilt: row.is_prebuilt,
            definitions: row.definitions,
          }));

        if (cancelled) return;
        setAvailableSavedWorkflows(next);
        if (!selectedSavedWorkflowKeys.length && next.length) {
          const selected = next.find((workflow) => workflow.name === selectedWorkflowName);
          const first = selected || next[0];
          setSelectedSavedWorkflowKeys(first ? [workflowKey(first)] : []);
        }
      } catch (err) {
        if (!cancelled) setError(errorMessage(err));
      } finally {
        if (!cancelled) setLoading(null);
      }
    }

    loadWorkflows();
    return () => {
      cancelled = true;
    };
  }, [selectedSavedWorkflowKeys.length, selectedWorkflowName, source, supabase]);

  useEffect(() => {
    if (selectedSavedWorkflowKeys.length || !availableSavedWorkflows.length) return;
    const selected = availableSavedWorkflows.find((workflow) => workflow.name === selectedWorkflowName);
    const first = selected || availableSavedWorkflows[0];
    setSelectedSavedWorkflowKeys(first ? [workflowKey(first)] : []);
  }, [availableSavedWorkflows, selectedSavedWorkflowKeys.length, selectedWorkflowName]);

  const hasCanvasWorkflow = nodes.length > 0;
  const canAnalyze = useMemo(() => {
    if (loading) return false;
    if (source === "current") return hasCanvasWorkflow;
    return selectedSavedWorkflowKeys.length > 0;
  }, [hasCanvasWorkflow, loading, selectedSavedWorkflowKeys.length, source]);

  const dependencyGraph = useMemo(() => preview?.preview?.dependency_graph || {}, [preview?.preview?.dependency_graph]);
  const executionOrder = useMemo(() => preview?.preview?.execution_order || [], [preview?.preview?.execution_order]);
  const parallelGroupAgents = useMemo(() => preview?.preview?.parallel_group_agents || [], [preview?.preview?.parallel_group_agents]);
  const resultErrors = preview?.errors || validation?.errors || [];
  const resultWarnings = preview?.warnings || validation?.warnings || [];
  const activeComposedWorkflow = composedWorkflow || currentComposedWorkflow();
  const agentSourcesByName = useMemo(() => {
    const sourcesByName = new Map<string, string[]>();
    if (!activeComposedWorkflow) return sourcesByName;
    activeComposedWorkflow.nodes.forEach((node) => {
      const agentName = agentLabelFromNode(node);
      const sources = activeComposedWorkflow.agentSources[node.id] || activeComposedWorkflow.sourceNames;
      sourcesByName.set(agentName, uniqueStrings([...(sourcesByName.get(agentName) || []), ...sources]));
    });
    return sourcesByName;
  }, [activeComposedWorkflow]);
  const displaySerialSteps = useMemo(() => {
    const seen = new Set<string>();
    const composedSteps = activeComposedWorkflow?.originalSerialSteps || [];
    const sourceSteps = composedSteps.length
      ? composedSteps
      : executionOrder.map((nodeId) => ({
          agentName: dependencyGraph[nodeId]?.agent_name || nodeId,
          sources: [],
          shared: false,
        }));
    return sourceSteps.filter((step) => {
      if (seen.has(step.agentName)) return false;
      seen.add(step.agentName);
      return true;
    }).map((step) => {
      const sources = uniqueStrings([...(agentSourcesByName.get(step.agentName) || []), ...step.sources]);
      return {
        ...step,
        sources,
        shared: sources.length > 1 || step.shared,
      };
    });
  }, [activeComposedWorkflow?.originalSerialSteps, agentSourcesByName, dependencyGraph, executionOrder]);
  const serialStageCount = displaySerialSteps.length;
  const parallelStageCount = parallelGroupAgents.length;
  const parallelizableGroupCount = parallelGroupAgents.filter((group) => group.length > 1).length;
  const stageReduction = Math.max(0, serialStageCount - parallelStageCount);
  const originalStepCount = activeComposedWorkflow?.originalStepCount || serialStageCount;
  const composedStepCount = activeComposedWorkflow?.nodes.length || serialStageCount;
  const sharedStepsRemoved = Math.max(0, originalStepCount - composedStepCount);

  function resetResults() {
    setPreview(null);
    setValidation(null);
    setError(null);
    setSaveStatus(null);
  }

  async function loadSavedWorkflowDefinition(workflow: SavedWorkflowOption) {
    if (workflow.definitions?.nodes?.length) {
      return {
        workflow,
        definitions: workflow.definitions,
        loopType: workflow.loop_type || loopType,
      };
    }

    const userId = await getStableUserId();
    let data: SavedWorkflowRecord | null = null;
    let dbError: { message?: string } | null = null;

    if (workflow.id) {
      const result = await supabase
        .from("workflows")
        .select("name,loop_type,definitions")
        .eq("id", workflow.id)
        .maybeSingle();
      data = result.data as SavedWorkflowRecord | null;
      dbError = result.error;
    } else if (workflow.is_prebuilt) {
      const result = await supabase
        .from("workflows")
        .select("name,loop_type,definitions")
        .eq("name", workflow.name)
        .eq("is_prebuilt", true)
        .maybeSingle();
      data = result.data as SavedWorkflowRecord | null;
      dbError = result.error;
    } else {
      const result = await supabase
        .from("workflows")
        .select("name,loop_type,definitions")
        .eq("user_id", userId)
        .eq("name", workflow.name)
        .maybeSingle();
      data = result.data as SavedWorkflowRecord | null;
      dbError = result.error;
    }

    if (dbError) throw new Error(dbError.message);
    if (!data?.definitions) throw new Error(`${workflow.name} has no graph definitions.`);

    return {
      workflow,
      definitions: data.definitions,
      loopType: data.loop_type || workflow.loop_type || loopType,
    };
  }

  async function buildSavedWorkflowPayload() {
    const selected = availableSavedWorkflows.filter((workflow) => selectedSavedWorkflowKeys.includes(workflowKey(workflow)));
    if (!selected.length) {
      throw new Error("Choose one or more saved workflows first.");
    }

    setLoading("saved");
    const loaded = await Promise.all(selected.map((workflow) => loadSavedWorkflowDefinition(workflow)));
    const payloadLoopType = loaded[0]?.loopType || loopType;
    const composed =
      suggestCompositionEdges && loaded.length === 1
        ? suggestBranchWorkflowFromCurrent(
            loaded[0].definitions.nodes || [],
            payloadLoopType,
            loaded[0].workflow.name,
            loaded[0].definitions.edges || [],
          )
        : composeWorkflowFromDefinitions(loaded, payloadLoopType, suggestCompositionEdges);
    setComposedWorkflow(composed);
    return graphPayloadFromComposedWorkflow(composed, suggestCompositionEdges);
  }

  async function runPreview(payloadOverride?: unknown) {
    setLoading("preview");
    setError(null);
    try {
      const payload = payloadOverride || parseJson(jsonText);
      setJsonText(JSON.stringify(payload, null, 2));
      const response = await apiPost<DagPreviewResponse>("/studio/dag/preview", payload);
      setPreview(response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  async function analyzeParallelism() {
    if (!canAnalyze) return;
    resetResults();
    try {
      let payload: unknown;
      if (source === "current" && suggestCurrentBranches) {
        const composed = suggestBranchWorkflowFromCurrent(nodes, loopType, "Current workflow", edges);
        setComposedWorkflow(composed);
        payload = graphPayloadFromComposedWorkflow(composed, true);
      } else {
        payload = source === "current"
          ? graphPayloadFromNodes(nodes, edges, loopType)
          : await buildSavedWorkflowPayload();
      }
      await runPreview(payload);
    } catch (err) {
      setError(errorMessage(err));
      setLoading(null);
    }
  }

  async function runValidate() {
    setLoading("validate");
    setError(null);
    try {
      const payload = parseJson(jsonText);
      const response = await apiPost<DagValidateResponse>("/studio/dag/validate", payload);
      setValidation(response);
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(null);
    }
  }

  function currentComposedWorkflow(): ComposedWorkflow | null {
    if (source === "saved" || (source === "current" && suggestCurrentBranches && composedWorkflow)) return composedWorkflow;
    if (!nodes.length) return null;
    return {
      nodes: nodes as Node[],
      edges: edges as Edge[],
      loopType,
      sourceNames: selectedWorkflowName ? [selectedWorkflowName] : ["Current workflow"],
      originalStepCount: nodes.length,
      originalSerialSteps: workflowSerialNodes(nodes, edges).map((node) => ({
        agentName: agentLabelFromNode(node),
        sources: selectedWorkflowName ? [selectedWorkflowName] : ["Current workflow"],
        shared: false,
      })),
      agentSources: Object.fromEntries(nodes.map((node) => [node.id, selectedWorkflowName ? [selectedWorkflowName] : ["Current workflow"]])),
    };
  }

  function openComposedWorkflow() {
    const composed = currentComposedWorkflow();
    if (!composed || !onOpenComposedWorkflow) return;
    const name = `Composed_${composed.sourceNames.join("_").replace(/[^a-zA-Z0-9_-]/g, "_")}`.slice(0, 80);
    onOpenComposedWorkflow({
      nodes: composed.nodes,
      edges: composed.edges,
      name,
      loopType: composed.loopType,
    });
    onClose();
  }

  async function saveComposedWorkflow() {
    const composed = currentComposedWorkflow();
    if (!composed) {
      setError("Analyze or compose a workflow before saving.");
      return;
    }
    const defaultName = `Composed_${composed.sourceNames.join("_").replace(/[^a-zA-Z0-9_-]/g, "_")}`.slice(0, 80);
    const workflowName = window.prompt("Save composed workflow as:", defaultName);
    if (!workflowName?.trim()) return;

    setSaveStatus("Saving composed workflow...");
    setError(null);
    try {
      const userId = await getStableUserId();
      const response = await fetch("/api/save_custom_workflow", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          user_id: userId,
          workflow: {
            workflow_name: workflowName.trim(),
            goal: "Composed workflow",
            summary: `Composed from: ${composed.sourceNames.join(", ")}`,
            loop_type: composed.loopType.toLowerCase(),
            nodes: composed.nodes,
            edges: composed.edges,
          },
        }),
      });
      if (!response.ok) throw new Error("Failed to save composed workflow.");
      window.dispatchEvent(new Event("refreshWorkflows"));
      setSaveStatus(`Saved "${workflowName.trim()}".`);
    } catch (err) {
      setError(errorMessage(err));
      setSaveStatus(null);
    }
  }

  function sourceText(sources: string[]): string {
    if (!sources.length) return "";
    return sources.length > 1 ? `Used by: ${sources.join(", ")}` : `From: ${sources[0]}`;
  }

  function sourcesForAgent(agentName: string): string[] {
    return agentSourcesByName.get(normalizeAgentName(agentName)) || [];
  }

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 p-4">
      <div className="flex max-h-[90vh] w-full max-w-5xl flex-col overflow-hidden rounded-2xl border border-slate-800 bg-slate-950 text-white shadow-2xl">
        <div className="flex items-start justify-between gap-4 border-b border-slate-800 p-5">
          <div>
            <h2 className="text-2xl font-extrabold text-cyan-300">Workflow Composer</h2>
            <p className="mt-1 text-sm text-slate-400">
              Start from a current or saved workflow, inspect its dependency structure, and analyze safe parallel stages before running.
            </p>
          </div>
          <button
            onClick={onClose}
            className="rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-300 hover:bg-slate-900"
          >
            Close
          </button>
        </div>

        <div className="min-h-0 overflow-y-auto p-5 scrollbar-thin scrollbar-thumb-slate-700 scrollbar-track-transparent">
          <section className="grid gap-4 rounded-lg border border-slate-800 bg-black/30 p-4 md:grid-cols-[220px_1fr_auto]">
            <div>
              <label className="mb-2 block text-xs font-semibold uppercase text-slate-500">Workflow source</label>
              <select
                value={source}
                onChange={(event) => {
                  setSource(event.target.value as "current" | "saved");
                  resetResults();
                }}
                className="w-full rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-200 outline-none focus:border-cyan-600"
              >
                <option value="current">Current workflow</option>
                <option value="saved">Saved workflow</option>
              </select>
            </div>

            <div>
              <label className="mb-2 block text-xs font-semibold uppercase text-slate-500">
                {source === "current" ? "Canvas workflow" : "Saved workflows"}
              </label>
              {source === "current" ? (
                <div>
                  <div className="rounded-lg border border-slate-800 bg-slate-950 px-3 py-2 text-sm text-slate-300">
                    {hasCanvasWorkflow ? `${nodes.length} agents on canvas` : "No agents on canvas"}
                  </div>
                  <label className="mt-2 flex items-center gap-2 text-xs text-slate-300">
                    <input
                      type="checkbox"
                      checked={suggestCurrentBranches}
                      onChange={(event) => {
                        setSuggestCurrentBranches(event.target.checked);
                        resetResults();
                      }}
                      className="h-4 w-4 accent-cyan-500"
                    />
                    Suggest branch structure from current workflow
                  </label>
                </div>
              ) : (
                <div>
                  <div className="max-h-40 overflow-y-auto rounded-lg border border-slate-700 bg-slate-950 p-2">
                  {availableSavedWorkflows.length ? (
                    availableSavedWorkflows.map((workflow) => {
                        const key = workflowKey(workflow);
                        const checked = selectedSavedWorkflowKeys.includes(key);
                        return (
                          <label key={key} className="flex cursor-pointer items-center gap-2 rounded px-2 py-1.5 text-sm text-slate-200 hover:bg-slate-900">
                            <input
                              type="checkbox"
                              checked={checked}
                              onChange={(event) => {
                                setSelectedSavedWorkflowKeys((prev) =>
                                  event.target.checked ? Array.from(new Set([...prev, key])) : prev.filter((item) => item !== key),
                                );
                                resetResults();
                              }}
                              className="h-4 w-4 accent-cyan-500"
                            />
                            <span>{workflowLabel(workflow)}</span>
                          </label>
                        );
                      })
                    ) : (
                      <div className="px-2 py-1.5 text-sm text-slate-500">
                        {loading === "saved" ? "Loading workflows..." : "No Supabase saved workflows found"}
                      </div>
                    )}
                  </div>
                  <label className="mt-2 flex items-center gap-2 text-xs text-slate-300">
                    <input
                      type="checkbox"
                      checked={suggestCompositionEdges}
                      onChange={(event) => {
                        setSuggestCompositionEdges(event.target.checked);
                        resetResults();
                      }}
                      className="h-4 w-4 accent-cyan-500"
                    />
                    Suggest branch structure and join edges
                  </label>
                </div>
              )}
            </div>

            <div className="flex items-end">
              <button
                onClick={analyzeParallelism}
                disabled={!canAnalyze}
                className="w-full rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500 md:w-auto"
              >
                {loading ? "Analyzing..." : "Analyze Parallelism"}
              </button>
            </div>
          </section>

          <div className="mt-4 rounded-lg border border-amber-800/60 bg-amber-950/20 p-3 text-xs text-amber-100/80">
            Composer analysis does not execute agents. Save as Private Workflow or Open on Canvas when the suggested graph looks right.
          </div>

          {error ? (
            <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 p-3 text-sm text-red-200">
              {error}
            </div>
          ) : null}

          {saveStatus ? (
            <div className="mt-4 rounded-lg border border-emerald-900/70 bg-emerald-950/30 p-3 text-sm text-emerald-200">
              {saveStatus}
            </div>
          ) : null}

          {!preview && !validation && !error ? (
            <div className="mt-4">
              <EmptyState />
            </div>
          ) : null}

          {preview ? (
            <div className="mt-5 space-y-4">
              <section className="grid gap-4 md:grid-cols-3">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Validation</div>
                  <div className={`mt-2 text-lg font-bold ${preview.valid ? "text-emerald-300" : "text-amber-300"}`}>
                    {preview.valid ? "Safe to review" : "Needs attention"}
                  </div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Estimated benefit</div>
                  <div className="mt-2 text-lg font-bold text-cyan-300">
                    {stageReduction > 0 ? `${stageReduction} fewer stages` : "No stage reduction yet"}
                  </div>
                  <div className="mt-1 text-xs text-slate-400">
                    {serialStageCount} serial steps to {parallelStageCount || 0} parallel stages
                  </div>
                </div>
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <div className="text-xs uppercase text-slate-500">Parallel groups</div>
                  <div className="mt-2 text-lg font-bold text-cyan-300">{parallelizableGroupCount}</div>
                  <div className="mt-1 text-xs text-slate-400">Groups with more than one agent</div>
                </div>
              </section>

              <section className="grid gap-3 rounded-lg border border-slate-800 bg-black/30 p-4 sm:grid-cols-2 lg:grid-cols-5">
                <div>
                  <div className="text-xs uppercase text-slate-500">Selected workflows</div>
                  <div className="mt-1 text-lg font-bold text-slate-100">{activeComposedWorkflow?.sourceNames.length || 1}</div>
                </div>
                <div>
                  <div className="text-xs uppercase text-slate-500">Original steps</div>
                  <div className="mt-1 text-lg font-bold text-slate-100">{originalStepCount}</div>
                </div>
                <div>
                  <div className="text-xs uppercase text-slate-500">Shared removed</div>
                  <div className="mt-1 text-lg font-bold text-emerald-300">{sharedStepsRemoved}</div>
                </div>
                <div>
                  <div className="text-xs uppercase text-slate-500">Composed steps</div>
                  <div className="mt-1 text-lg font-bold text-cyan-300">{composedStepCount}</div>
                </div>
                <div>
                  <div className="text-xs uppercase text-slate-500">Parallel groups</div>
                  <div className="mt-1 text-lg font-bold text-cyan-300">{parallelizableGroupCount}</div>
                </div>
              </section>

              <section className="grid gap-4 lg:grid-cols-2">
                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <h3 className="mb-3 text-sm font-bold text-cyan-300">Current Serial Steps</h3>
                  {displaySerialSteps.length ? (
                    <ol className="space-y-2 text-sm text-slate-300">
                      {displaySerialSteps.map((step, index) => (
                        <li key={`${step.agentName}-${index}`} className="rounded border border-slate-800 bg-slate-950 px-3 py-2">
                          <div className="flex flex-wrap items-center gap-2">
                            <span className="text-slate-500">Step {index + 1}</span>
                            <span>{step.agentName}</span>
                            {step.shared ? (
                              <span className="rounded-full border border-emerald-900/70 bg-emerald-950/40 px-2 py-0.5 text-[11px] font-semibold uppercase text-emerald-200">
                                Shared step
                              </span>
                            ) : null}
                          </div>
                          {sourceText(step.sources) ? (
                            <div className="mt-1 text-xs text-slate-500">{sourceText(step.sources)}</div>
                          ) : null}
                        </li>
                      ))}
                    </ol>
                  ) : (
                    <div className="text-sm text-slate-500">No serial order returned.</div>
                  )}
                </div>

                <div className="rounded-lg border border-slate-800 bg-black/30 p-4">
                  <h3 className="mb-3 text-sm font-bold text-cyan-300">Parallel Stages Found</h3>
                  {parallelGroupAgents.length ? (
                    <div className="space-y-3 text-sm text-slate-300">
                      {parallelGroupAgents.map((group, index) => (
                        <div key={`group-${index}`} className="rounded border border-slate-800 bg-slate-950 p-3">
                          <div className="mb-2 text-xs font-semibold uppercase text-slate-500">Stage {index + 1}</div>
                          <div className="flex flex-wrap gap-2">
                            {group.map((agent) => {
                              const sources = sourcesForAgent(agent);
                              return (
                                <span key={`${index}-${agent}`} className="rounded-lg border border-cyan-900/60 bg-cyan-950/30 px-2 py-1 text-xs text-cyan-100">
                                  <span>{agent}</span>
                                  {sources.length ? (
                                    <span className="ml-1 text-cyan-200/70">
                                      - {sources.length > 1 ? `Shared: ${sources.join(", ")}` : sources[0]}
                                    </span>
                                  ) : null}
                                </span>
                              );
                            })}
                          </div>
                        </div>
                      ))}
                    </div>
                  ) : (
                    <div className="text-sm text-slate-500">No parallel groups returned.</div>
                  )}
                </div>
              </section>

              <section className="rounded-lg border border-slate-800 bg-black/30 p-4">
                <h3 className="mb-3 text-sm font-bold text-cyan-300">Warnings</h3>
                {resultWarnings.length || resultErrors.length ? (
                  <ul className="space-y-2 text-sm">
                    {[...resultWarnings, ...resultErrors].map((item, index) => (
                      <li key={`${item}-${index}`} className="rounded border border-amber-900/60 bg-amber-950/20 px-3 py-2 text-amber-100">
                        {item}
                      </li>
                    ))}
                  </ul>
                ) : (
                  <div className="text-sm text-slate-400">
                    No blocking warnings returned. Review the stages before creating any future composed workflow version.
                  </div>
                )}
              </section>

              <section className="flex flex-wrap justify-end gap-2">
                <button
                  onClick={openComposedWorkflow}
                  disabled={!currentComposedWorkflow()}
                  className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                >
                  Open on Canvas
                </button>
                <button
                  onClick={saveComposedWorkflow}
                  disabled={!currentComposedWorkflow()}
                  className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500"
                >
                  Save as Private Workflow
                </button>
                <button
                  onClick={() => setAdvancedOpen((open) => !open)}
                  className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-900"
                >
                  {advancedOpen ? "Hide JSON Details" : "JSON Details"}
                </button>
              </section>
            </div>
          ) : null}

          <section className="mt-5 rounded-lg border border-slate-800 bg-black/20">
            <button
              onClick={() => setAdvancedOpen((open) => !open)}
              className="flex w-full items-center justify-between px-4 py-3 text-left text-sm font-semibold text-slate-200 hover:bg-slate-900"
            >
              <span>JSON Details and Dependency Debug</span>
              <span className="text-slate-500">{advancedOpen ? "Hide" : "Show"}</span>
            </button>

            {advancedOpen ? (
              <div className="space-y-4 border-t border-slate-800 p-4">
                <p className="text-sm text-slate-400">
                  Optional: inspect or validate the workflow JSON sent to the analyzer. Most users can use Analyze Parallelism and Save as Private Workflow above.
                </p>
                <div>
                  <label className="block text-sm font-semibold text-slate-200">Workflow plan JSON</label>
                  <textarea
                    value={jsonText}
                    onChange={(event) => setJsonText(event.target.value)}
                    className="mt-2 h-56 w-full resize-none rounded-lg border border-slate-700 bg-black/40 p-3 font-mono text-xs outline-none focus:border-cyan-600"
                    spellCheck={false}
                  />
                  <div className="mt-3 flex flex-wrap gap-2">
                    <button
                      onClick={() => {
                        setJsonText(JSON.stringify(graphPayloadFromNodes(nodes, edges, loopType), null, 2));
                        resetResults();
                      }}
                      disabled={!hasCanvasWorkflow}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                    >
                      Use current workflow JSON
                    </button>
                    <button
                      onClick={() => {
                        setJsonText(JSON.stringify(samplePayload(loopType), null, 2));
                        resetResults();
                      }}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs text-slate-200 hover:bg-slate-900"
                    >
                      Use sample JSON
                    </button>
                    <button
                      onClick={() => runPreview()}
                      disabled={Boolean(loading) || !jsonText.trim()}
                      className="rounded-lg bg-cyan-600 px-3 py-2 text-xs font-bold text-white hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
                    >
                      Preview from JSON
                    </button>
                    <button
                      onClick={runValidate}
                      disabled={Boolean(loading) || !jsonText.trim()}
                      className="rounded-lg border border-slate-700 px-3 py-2 text-xs font-semibold text-slate-200 hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
                    >
                      Validate
                    </button>
                  </div>
                </div>

                {preview || validation ? (
                  <div className="space-y-4">
                    <section className="grid gap-4 lg:grid-cols-2">
                      <JsonBlock title="Nodes" value={preview?.dag?.nodes || []} />
                      <JsonBlock title="Edges" value={preview?.dag?.edges || []} />
                    </section>
                    <section className="grid gap-4 lg:grid-cols-2">
                      <JsonBlock title="Parallel Groups" value={preview?.preview?.parallel_groups || []} />
                      <JsonBlock title="Dependency Graph" value={preview?.preview?.dependency_graph || {}} />
                    </section>
                  </div>
                ) : null}
              </div>
            ) : null}
          </section>
        </div>
      </div>
    </div>
  );
}
