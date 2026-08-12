"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { HemAutomaticRunControls, HemChildDashboardLinks } from "@/components/HemAutomaticRun";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const supabase = createClientComponentClient();

type PhysicsModel = { model_id: string; name: string; provider: string; domain: string; runtime: string; availability: string; gpu_required: boolean };
type ExecutionMode = "architecture" | "cpu_reference" | "validated";
type ImplementationPath = "architecture_only" | "digital_ip_asic" | "fpga_prototype" | "fpga_then_asic";
type DeploymentArchitecture = "automatic" | "fpga_onboard_cpu" | "fpga_soft_cpu" | "fpga_external_host" | "asic_digital_ip" | "asic_soc" | "asic_companion";

const paths: Array<{ key: ImplementationPath; title: string; body: string }> = [
  { key: "architecture_only", title: "Architecture only", body: "Stop after the architecture and digital-IP plan." },
  { key: "digital_ip_asic", title: "ASIC / Digital IP", body: "Generate and verify RTL, then run Arch2Tapeout." },
  { key: "fpga_prototype", title: "FPGA prototype", body: "Generate and verify RTL, explore boards, select one, and generate the bitstream." },
  { key: "fpga_then_asic", title: "FPGA, then ASIC", body: "Prototype on FPGA first, then continue through Arch2Tapeout." },
];

type RunSummary = { status?: string; physics_model?: { name?: string }; physics_execution?: { execution_mode?: string; inference_status?: string; implementation_path?: string }; hem?: { enabled?: boolean } };
type HemChildRun = { workflow_id: string; label: string; status?: string | null; phase?: string | null; logs?: string | null; dashboard_path: string };
type ApiPayload = { status?: string; phase?: string; logs?: string; hem_children?: unknown; result?: RunSummary; detail?: string; workflow_id?: string };

async function readApiPayload(response: Response): Promise<ApiPayload> {
  const body = await response.text();
  if (!body.trim()) return {};
  try {
    return JSON.parse(body) as ApiPayload;
  } catch {
    return { detail: `Physical AI backend returned HTTP ${response.status}: ${body.slice(0, 300)}` };
  }
}

function mergeHemChildren(previous: HemChildRun[], incoming: unknown): HemChildRun[] {
  if (!Array.isArray(incoming)) return previous;
  const byWorkflowId = new Map(previous.map((child) => [child.workflow_id, child]));
  for (const raw of incoming) {
    if (!raw || typeof raw !== "object") continue;
    const child = raw as Partial<HemChildRun>;
    if (!child.workflow_id || !child.label || !child.dashboard_path) continue;
    byWorkflowId.set(child.workflow_id, { ...byWorkflowId.get(child.workflow_id), ...child } as HemChildRun);
  }
  return Array.from(byWorkflowId.values());
}

function activeAgentFromLogs(logs: string): { agent: string; stage: string } | null {
  const lines = logs.split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  for (let index = lines.length - 1; index >= 0; index -= 1) {
    const line = lines[index];
    if (line.startsWith("AGENT COMPLETED:") || line.startsWith("AGENT FAILED:")) return null;
    const match = line.match(/^ACTIVE AGENT:\s*(.+?)\s*\|\s*Stage:\s*(.+)$/);
    if (match) return { agent: match[1].trim(), stage: match[2].trim() };
    const physicalAiMatch = line.match(/^Physical AI agent started:\s*(.+)$/i);
    if (physicalAiMatch) return { agent: physicalAiMatch[1].trim(), stage: "Physical AI" };
    if (/^Physical AI agent (completed|failed):/i.test(line)) return null;
  }
  return null;
}

export default function PhysicalAiStudioPage() {
  const router = useRouter();
  const [token, setToken] = useState<string | null>(null);
  const [models, setModels] = useState<PhysicsModel[]>([]);
  const [modelId, setModelId] = useState("chiploop.pmsm.dq.v1");
  const [objective, setObjective] = useState("Build and verify a safe motor-control digital IP");
  const [executionMode, setExecutionMode] = useState<ExecutionMode>("validated");
  const [implementationPath, setImplementationPath] = useState<ImplementationPath>("fpga_prototype");
  const [deploymentArchitecture, setDeploymentArchitecture] = useState<DeploymentArchitecture>("automatic");
  const [agentMode, setAgentMode] = useState<"standard" | "smart">("standard");
  const [standardModel, setStandardModel] = useState("chiploop_default");
  const [hemEnabled, setHemEnabled] = useState(true);
  const [hemAdaptive, setHemAdaptive] = useState(false);
  const [running, setRunning] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [workflowId, setWorkflowId] = useState<string | null>(null);
  const [runStatus, setRunStatus] = useState("queued");
  const [runPhase, setRunPhase] = useState("queued");
  const [runLogs, setRunLogs] = useState("");
  const [runResult, setRunResult] = useState<RunSummary | null>(null);
  const [hemChildren, setHemChildren] = useState<HemChildRun[]>([]);

  useEffect(() => {
    supabase.auth.getSession().then(async ({ data }) => {
      const applicationIntelligenceApp = typeof window !== "undefined" && window.location.pathname.includes("/apps/application-intelligence");
      if (!data.session) return router.replace(`/login?next=${applicationIntelligenceApp ? "/apps/application-intelligence" : "/apps/physical-ai"}`);
      setToken(data.session.access_token);
      const response = await fetch(`${API_BASE}/apps/physical-ai/models`, { headers: { Authorization: `Bearer ${data.session.access_token}` } });
      if (response.ok) setModels((await response.json()).models || []);
    });
  }, [router]);

  useEffect(() => {
    if (models.length === 0 || typeof window === "undefined") return;
    const applicationIntelligenceApp = window.location.pathname.includes("/apps/application-intelligence");
    if (applicationIntelligenceApp || ["pretrained-aero", "application-intelligence-aero"].includes(String(new URLSearchParams(window.location.search).get("reference")))) {
      setModelId("nvidia.domino.automotive_aero");
      setExecutionMode("cpu_reference");
      setImplementationPath("fpga_prototype");
      setObjective("Build an intelligent active-aerodynamics controller for 20–55 m/s operation. Evaluate NVIDIA DoMINO as the physics-based surrogate, establish a transparent reference, partition the system, define and optimize the architecture, and deliver the hardware, firmware, and software with bounded control, stale-data detection, timeout handling, and safe fallback.");
    } else if (new URLSearchParams(window.location.search).get("reference") === "motor") {
      setModelId("chiploop.pmsm.dq.v1");
      setExecutionMode("validated");
      setImplementationPath("fpga_prototype");
      setObjective("Build and verify a safe PMSM motor-control digital IP");
    }
  }, [models]);

  useEffect(() => {
    if (!workflowId || !token) return;
    let stopped = false;
    let timer: ReturnType<typeof setTimeout> | undefined;
    const poll = async () => {
      try {
        const response = await fetch(`${API_BASE}/apps/physical-ai/${workflowId}/result`, { headers: { Authorization: `Bearer ${token}` }, cache: "no-store" });
        const payload = await readApiPayload(response);
        if (stopped) return;
        setRunStatus(String(payload.status || "running"));
        setRunPhase(String(payload.phase || payload.status || "running"));
        setRunLogs(String(payload.logs || ""));
        setHemChildren((previous) => mergeHemChildren(previous, payload.hem_children));
        if (payload.result) setRunResult(payload.result as RunSummary);
        const normalizedPhase = String(payload.phase || "").toLowerCase();
        const hemIsRunning = Boolean(payload.result?.hem?.enabled);
        const terminal = ["hem_complete", "hem_failed", "architecture_complete", "needs_revision", "error"].includes(normalizedPhase) || (!hemIsRunning && normalizedPhase === "digital_design_ready");
        if (!terminal && response.status !== 409) timer = setTimeout(poll, 1500);
      } catch (cause) {
        if (!stopped) {
          setError(cause instanceof Error ? cause.message : String(cause));
          timer = setTimeout(poll, 3000);
        }
      }
    };
    poll();
    return () => { stopped = true; if (timer) clearTimeout(timer); };
  }, [token, workflowId]);

  const selected = models.find((model) => model.model_id === modelId);
  const journeyLogs = useMemo(() => {
    const sections = runLogs.trim() ? [runLogs.trim()] : [];
    for (const child of hemChildren) {
      const childLogs = String(child.logs || "").trim();
      if (childLogs) sections.push(`[${child.label} · ${child.status || "running"}]\n${childLogs}`);
    }
    return sections.join("\n\n");
  }, [hemChildren, runLogs]);
  const activeAgent = useMemo(() => activeAgentFromLogs(journeyLogs), [journeyLogs]);
  const validatedAvailable = selected?.availability === "ready";
  const stages = useMemo(() => {
    const base = ["Application", "Model mapping", "Partition", "Architecture", "RTL generation", "Verification"];
    if (implementationPath === "architecture_only") return base.slice(0, 4);
    const product = ["Device layer", "Software", "Validation", "Product"];
    if (implementationPath === "fpga_prototype") return [...base, "Board explorer", "Bitstream", ...product];
    if (implementationPath === "digital_ip_asic") return [...base, "ASIC implementation", ...product];
    return [...base, "Board explorer", "Bitstream", "ASIC implementation", ...product];
  }, [implementationPath]);
  const deploymentOptions = useMemo(() => {
    if (implementationPath.includes("fpga")) return [
      { key: "automatic", title: "Choose automatically", body: "Refine after FPGA Explorer selects a viable board." },
      { key: "fpga_onboard_cpu", title: "Onboard CPU", body: "Use a hard CPU connected to FPGA fabric." },
      { key: "fpga_soft_cpu", title: "Soft CPU", body: "Implement a CPU in FPGA logic and reserve its resources." },
      { key: "fpga_external_host", title: "External host", body: "Use a PC, Mac, MCU, or embedded host over a board transport." },
    ] as const;
    return [
      { key: "automatic", title: "Choose automatically", body: "Select the ASIC integration model from the requirements." },
      { key: "asic_digital_ip", title: "Digital IP", body: "Deliver reusable IP; the customer supplies the CPU." },
      { key: "asic_soc", title: "ASIC SoC", body: "Include an embedded CPU, interconnect, firmware, and software." },
      { key: "asic_companion", title: "Companion ASIC", body: "Use an external processor through a defined transport." },
    ] as const;
  }, [implementationPath]);

  useEffect(() => {
    if (!deploymentOptions.some((option) => option.key === deploymentArchitecture)) setDeploymentArchitecture("automatic");
  }, [deploymentArchitecture, deploymentOptions]);

  async function start() {
    if (!token || !selected || running) return;
    if (executionMode === "validated" && !validatedAvailable) {
      setError("Validated surrogate execution needs a connected NIM or GPU worker. Choose Architecture mode for this model.");
      return;
    }
    setRunning(true);
    setError(null);
    const motor = selected.domain === "motor_control";
    try {
      const response = await fetch(`${API_BASE}/apps/physical-ai/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", Authorization: `Bearer ${token}` },
        body: JSON.stringify({
          journey_id: typeof window !== "undefined" && window.location.pathname.includes("/apps/application-intelligence") ? "application_intelligence_active_aero" : "physical_ai_studio",
          application: motor ? "pmsm_motor_control" : "intelligent_active_aerodynamics_controller",
          objective,
          physics_domain: selected.domain,
          physics_model_id: selected.model_id,
          execution_mode: executionMode,
          implementation_path: implementationPath,
          deployment_architecture: deploymentArchitecture,
          implementation_target: implementationPath.includes("fpga") ? "fpga" : "asic",
          generate_architecture_with_model: true,
          parameters: motor
            ? { dc_bus_voltage_v: 48, rated_speed_rpm: 3000, load_torque_nm: 0.15, control_loop_hz: 20000 }
            : { stream_velocity_mps: 38.89, geometry_format: "STL", geometry_source: "DrivAerML reference geometry" },
          operating_envelope: motor ? { speed_rpm: [0, 3000], load_torque_nm: [0, 0.15] } : { stream_velocity_mps: [20, 55] },
          safety_constraints: motor ? ["Limit current", "Keep winding temperature below 120 C"] : ["Reject stale model commands", "Clamp actuator commands", "Provide a safe fallback"],
          model_policy: { mode: agentMode, selected_model: standardModel },
          hem_enabled: hemEnabled && implementationPath !== "architecture_only",
          hem_mode: hemAdaptive ? "adaptive" : "fixed",
          hem_goal: "product_demo",
        }),
      });
      const data = await readApiPayload(response);
      if (!response.ok) throw new Error(String(data.detail || `Unable to start Physical AI journey (HTTP ${response.status})`));
      setWorkflowId(String(data.workflow_id));
      setRunStatus("running");
      setRunPhase("queued");
    } catch (cause) {
      setError(cause instanceof Error ? cause.message : String(cause));
      setRunning(false);
    }
  }

  if (workflowId) {
    const complete = ["hem_complete", "hem_failed", "architecture_complete", "needs_revision", "error"].includes(
      runPhase.toLowerCase(),
    );
    return <main className="min-h-screen bg-slate-950 text-white"><div className="mx-auto max-w-7xl px-6 py-10">
      <div className="flex flex-wrap items-center justify-between gap-3"><button onClick={() => { setWorkflowId(null); setRunResult(null); setRunLogs(""); setHemChildren([]); setRunning(false); }} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Configure another run</button><span className={`rounded-full px-3 py-2 text-xs font-bold uppercase ${runPhase === "hem_failed" || runPhase === "error" ? "bg-red-500/15 text-red-200" : complete ? "bg-lime-500/15 text-lime-200" : "bg-cyan-500/15 text-cyan-200"}`}>{runPhase.replaceAll("_", " ")}</span></div>
      <div className="mt-8 flex flex-wrap items-end justify-between gap-4"><div><div className="text-xs font-bold uppercase tracking-widest text-fuchsia-300">Physical AI reference journey</div><h1 className="mt-2 text-4xl font-extrabold">{complete ? "Run dashboard" : "Physical AI agents are running"}</h1><p className="mt-3 text-slate-400">Workflow {workflowId}</p></div><a href={`/dashboard/${workflowId}?stage=physical_ai&app=PhysicalAI`} target="_blank" rel="noreferrer" className="rounded-xl border border-cyan-400 px-5 py-3 text-sm font-bold text-cyan-200">Open Dashboard ↗</a></div>
      <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><h2 className="text-xl font-bold">Running log</h2><p className="mt-1 text-sm text-slate-400">Agents and automatic child workflows appear here in execution order.</p></div><span className="rounded-full border border-slate-700 px-3 py-1 text-xs font-bold uppercase text-slate-300">{runPhase.replaceAll("_", " ")}</span></div>{activeAgent && <div className="mt-4 flex flex-wrap items-center gap-3 rounded-xl border border-cyan-400/30 bg-cyan-500/10 px-4 py-3"><span className="h-2.5 w-2.5 animate-pulse rounded-full bg-cyan-300" /><div><div className="text-xs font-bold uppercase tracking-wide text-cyan-300">Active agent</div><div className="mt-1 font-semibold text-white">{activeAgent.agent}</div></div><span className="ml-auto rounded-full bg-slate-950 px-3 py-1 text-xs text-slate-300">{activeAgent.stage}</span></div>}<pre className="mt-4 max-h-96 overflow-auto whitespace-pre-wrap rounded-xl bg-slate-950 p-4 text-xs leading-6 text-slate-300">{journeyLogs || "Waiting for the first agent…"}</pre></section>
      {runResult && <section className="mt-6 grid gap-4 md:grid-cols-3"><div className="rounded-xl border border-slate-800 bg-slate-900/50 p-5"><div className="text-xs uppercase text-slate-500">Physics model</div><div className="mt-2 font-bold">{runResult.physics_model?.name || "Selected model"}</div></div><div className="rounded-xl border border-slate-800 bg-slate-900/50 p-5"><div className="text-xs uppercase text-slate-500">Mode</div><div className="mt-2 font-bold capitalize">{(runResult.physics_execution?.execution_mode || "validated").replaceAll("_", " ")}</div></div><div className="rounded-xl border border-slate-800 bg-slate-900/50 p-5"><div className="text-xs uppercase text-slate-500">Implementation</div><div className="mt-2 font-bold capitalize">{(runResult.physics_execution?.implementation_path || implementationPath).replaceAll("_", " ")}</div></div></section>}
      <section className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/15 p-6"><h2 className="text-xl font-bold">HEM and next workflows</h2><p className="mt-2 text-sm text-slate-400">Automatic child workflows remain available here after completion or failure. If HEM is off, use the evidence dashboard to continue manually.</p><HemChildDashboardLinks logs={journeyLogs} runs={hemChildren} rootWorkflowId={workflowId} /></section>
      <div className="mt-6"><WorkflowEvidenceDashboard workflowId={workflowId} status={runStatus} stage="physical_ai" logs={runLogs} /></div>
      {error && <div className="mt-5 rounded-xl border border-red-500/30 bg-red-500/10 p-4 text-red-200">{error}</div>}
    </div></main>;
  }

  return <main className="min-h-screen bg-slate-950 text-white"><div className="mx-auto max-w-7xl px-6 py-10">
    <div className="flex items-center justify-between"><button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Back to Apps</button><span className="rounded-full border border-fuchsia-400/40 bg-fuchsia-500/10 px-3 py-1 text-xs font-bold text-fuchsia-200">Coming soon</span></div>
    <div className="mt-8 max-w-4xl"><div className="text-xs font-bold uppercase tracking-widest text-fuchsia-300">Application Intelligence reference journey</div><h1 className="mt-3 text-4xl font-extrabold">From application to an intelligent FPGA or ASIC system.</h1><p className="mt-3 text-slate-300">ChipLoop understands the application, maps an appropriate surrogate, partitions software, firmware, and hardware jobs, then reuses proven implementation loops.</p></div>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-fuchsia-300">1 · Application and physics model</div><label className="mt-4 block text-sm text-slate-300">What do you want to build?<textarea value={objective} onChange={(event) => setObjective(event.target.value)} className="mt-2 min-h-24 w-full rounded-xl border border-slate-700 bg-slate-950 p-4" /></label><div className="mt-5 grid gap-3 md:grid-cols-2">{models.map((model) => <button type="button" key={model.model_id} onClick={() => setModelId(model.model_id)} className={`rounded-xl border p-4 text-left ${modelId === model.model_id ? "border-fuchsia-400 bg-fuchsia-500/10" : "border-slate-700 bg-slate-950"}`}><div className="flex items-start justify-between gap-3"><div className="font-semibold">{model.name}</div><span className={`text-xs font-bold ${model.availability === "ready" ? "text-lime-300" : "text-amber-300"}`}>{model.availability === "ready" ? "Ready" : "Architecture ready"}</span></div><div className="mt-2 text-xs text-slate-400">{model.provider} · {model.gpu_required ? "GPU needed only for real inference" : "Runs on CPU"}</div></button>)}</div></section>

    <div className="mt-6 grid gap-6 lg:grid-cols-2"><section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-cyan-300">2 · How to use the model</div><div className="mt-4 space-y-3">{([{ key: "architecture", title: "Architecture only", body: "Map the pretrained model and define the product without executing physics." }, { key: "cpu_reference", title: "CPU reference", body: "Run transparent equations to exercise partitioning and implementation; pretrained inference remains explicitly not executed." }, { key: "validated", title: "Qualified surrogate inference", body: "Run the pretrained model and qualify its real results." }] as const).map((item) => <button type="button" key={item.key} disabled={item.key === "validated" && !validatedAvailable} onClick={() => setExecutionMode(item.key)} className={`w-full rounded-xl border p-4 text-left disabled:cursor-not-allowed disabled:opacity-40 ${executionMode === item.key ? "border-cyan-400 bg-cyan-500/10" : "border-slate-700"}`}><div className="font-semibold">{item.title}</div><div className="mt-1 text-xs text-slate-400">{item.body}</div>{item.key === "validated" && !validatedAvailable && <div className="mt-2 text-xs font-semibold text-amber-300">Connect NIM or a qualified GPU worker to enable</div>}</button>)}</div></section>
      <section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-violet-300">3 · Agent model</div><div className="mt-4 flex gap-3">{(["standard", "smart"] as const).map((item) => <button type="button" key={item} onClick={() => setAgentMode(item)} className={`rounded-lg border px-4 py-2 capitalize ${agentMode === item ? "border-violet-400 bg-violet-500/10" : "border-slate-700"}`}>{item}</button>)}</div>{agentMode === "standard" && <select value={standardModel} onChange={(event) => setStandardModel(event.target.value)} className="mt-4 w-full rounded-lg border border-slate-700 bg-slate-950 p-3"><option value="chiploop_default">ChipLoop default model</option><option value="nvidia_nemotron">NVIDIA Nemotron for every agent</option></select>}<p className="mt-4 text-xs text-slate-400">Smart mode selects the model for each agent. The chosen policy is saved with the run.</p></section></div>

    <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-lime-300">4 · Choose where the design goes</div><div className="mt-4 grid gap-3 md:grid-cols-2 xl:grid-cols-4">{paths.map((path) => <button type="button" key={path.key} onClick={() => setImplementationPath(path.key)} className={`rounded-xl border p-4 text-left ${implementationPath === path.key ? "border-lime-400 bg-lime-500/10" : "border-slate-700 bg-slate-950"}`}><div className="font-semibold">{path.title}</div><div className="mt-2 text-xs leading-5 text-slate-400">{path.body}</div></button>)}</div><div className="mt-6 overflow-x-auto"><div className="flex min-w-max items-center gap-2">{stages.map((stage, index) => <div key={stage} className="contents"><div className="w-36 rounded-xl border border-slate-700 bg-slate-950 p-3 text-center text-sm"><span className="mr-2 text-fuchsia-300">{index + 1}</span>{stage}</div>{index < stages.length - 1 && <span className="text-slate-500">→</span>}</div>)}</div></div></section>

    {implementationPath !== "architecture_only" && <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-amber-300">5 · CPU and host architecture</div><p className="mt-2 text-sm text-slate-400">Functional partitioning happens first. This choice controls target refinement and the firmware gate.</p><div className="mt-4 grid gap-3 md:grid-cols-2 xl:grid-cols-4">{deploymentOptions.map((option) => <button type="button" key={option.key} onClick={() => setDeploymentArchitecture(option.key)} className={`rounded-xl border p-4 text-left ${deploymentArchitecture === option.key ? "border-amber-400 bg-amber-500/10" : "border-slate-700 bg-slate-950"}`}><div className="font-semibold">{option.title}</div><div className="mt-2 text-xs leading-5 text-slate-400">{option.body}</div></button>)}</div></section>}

    {implementationPath !== "architecture_only" && <section className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/15 p-6"><HemAutomaticRunControls enabled={hemEnabled} adaptive={hemAdaptive} onEnabledChange={setHemEnabled} onAdaptiveChange={setHemAdaptive} currentStageLabel="Physical AI architecture" nextStageLabel="RTL generation" /><p className="mt-4 text-sm text-slate-400">When enabled, ChipLoop continues automatically through the selected path. When disabled, the completed dashboard shows the next workflow button.</p></section>}
    {error && <div className="mt-5 rounded-xl border border-red-500/30 bg-red-500/10 p-4 text-red-200">{error}</div>}
    <button onClick={start} disabled={!token || !selected || running} className="mt-6 w-full rounded-xl bg-fuchsia-400 px-6 py-4 text-lg font-bold text-slate-950 disabled:opacity-50">{running ? "Starting the journey…" : hemEnabled && implementationPath !== "architecture_only" ? "Run the complete journey" : "Run Physical AI agents"}</button>
  </div></main>;
}
