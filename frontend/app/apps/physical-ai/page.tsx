"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { HemAutomaticRunControls } from "@/components/HemAutomaticRun";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const supabase = createClientComponentClient();

type PhysicsModel = { model_id: string; name: string; provider: string; domain: string; runtime: string; availability: string; gpu_required: boolean };
type ExecutionMode = "architecture" | "validated";
type ImplementationPath = "architecture_only" | "digital_ip_asic" | "fpga_prototype" | "fpga_then_asic";

const paths: Array<{ key: ImplementationPath; title: string; body: string }> = [
  { key: "architecture_only", title: "Architecture only", body: "Stop after the architecture and digital-IP plan." },
  { key: "digital_ip_asic", title: "ASIC / Digital IP", body: "Generate and verify RTL, then run Arch2Tapeout." },
  { key: "fpga_prototype", title: "FPGA prototype", body: "Generate and verify RTL, explore boards, select one, and generate the bitstream." },
  { key: "fpga_then_asic", title: "FPGA, then ASIC", body: "Prototype on FPGA first, then continue through Arch2Tapeout." },
];

export default function PhysicalAiStudioPage() {
  const router = useRouter();
  const [token, setToken] = useState<string | null>(null);
  const [models, setModels] = useState<PhysicsModel[]>([]);
  const [modelId, setModelId] = useState("chiploop.pmsm.dq.v1");
  const [objective, setObjective] = useState("Build and verify a safe motor-control digital IP");
  const [executionMode, setExecutionMode] = useState<ExecutionMode>("validated");
  const [implementationPath, setImplementationPath] = useState<ImplementationPath>("fpga_prototype");
  const [agentMode, setAgentMode] = useState<"standard" | "smart">("standard");
  const [standardModel, setStandardModel] = useState("chiploop_default");
  const [hemEnabled, setHemEnabled] = useState(true);
  const [hemAdaptive, setHemAdaptive] = useState(false);
  const [running, setRunning] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    supabase.auth.getSession().then(async ({ data }) => {
      if (!data.session) return router.replace("/login?next=/apps/physical-ai");
      setToken(data.session.access_token);
      const response = await fetch(`${API_BASE}/apps/physical-ai/models`, { headers: { Authorization: `Bearer ${data.session.access_token}` } });
      if (response.ok) setModels((await response.json()).models || []);
    });
  }, [router]);

  useEffect(() => {
    if (models.length === 0 || typeof window === "undefined") return;
    if (new URLSearchParams(window.location.search).get("reference") === "pretrained-aero") {
      setModelId("nvidia.domino.automotive_aero");
      setExecutionMode("architecture");
      setImplementationPath("digital_ip_asic");
      setObjective("Build an AI-assisted active-aerodynamics controller using NVIDIA's pretrained DoMINO model interface");
    } else if (new URLSearchParams(window.location.search).get("reference") === "motor") {
      setModelId("chiploop.pmsm.dq.v1");
      setExecutionMode("validated");
      setImplementationPath("fpga_prototype");
      setObjective("Build and verify a safe PMSM motor-control digital IP");
    }
  }, [models]);

  const selected = models.find((model) => model.model_id === modelId);
  const validatedAvailable = selected?.availability === "ready";
  const stages = useMemo(() => {
    const base = ["Physical AI agents", "Architecture", "RTL generation", "Verification"];
    if (implementationPath === "architecture_only") return base.slice(0, 2);
    if (implementationPath === "fpga_prototype") return [...base, "Board explorer", "Bitstream"];
    if (implementationPath === "digital_ip_asic") return [...base, "ASIC implementation"];
    return [...base, "Board explorer", "Bitstream", "ASIC implementation"];
  }, [implementationPath]);

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
          application: motor ? "pmsm_motor_control" : "automotive_aerodynamics_architecture",
          objective,
          physics_domain: selected.domain,
          physics_model_id: selected.model_id,
          execution_mode: executionMode,
          implementation_path: implementationPath,
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
      const data = await response.json();
      if (!response.ok) throw new Error(data.detail || "Unable to start Physical AI journey");
      router.push(data.dashboard_path);
    } catch (cause) {
      setError(cause instanceof Error ? cause.message : String(cause));
      setRunning(false);
    }
  }

  return <main className="min-h-screen bg-slate-950 text-white"><div className="mx-auto max-w-7xl px-6 py-10">
    <div className="flex items-center justify-between"><button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Back to Apps</button><span className="rounded-full border border-fuchsia-400/40 bg-fuchsia-500/10 px-3 py-1 text-xs font-bold text-fuchsia-200">Coming soon</span></div>
    <div className="mt-8 max-w-4xl"><div className="text-xs font-bold uppercase tracking-widest text-fuchsia-300">Physical AI reference journey</div><h1 className="mt-3 text-4xl font-extrabold">Choose an application. Build an FPGA or ASIC product.</h1><p className="mt-3 text-slate-300">ChipLoop runs the Physical AI agents, creates an architecture using your selected agent model, generates and verifies RTL, and then follows your chosen implementation path.</p></div>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-fuchsia-300">1 · Application and physics model</div><label className="mt-4 block text-sm text-slate-300">What do you want to build?<textarea value={objective} onChange={(event) => setObjective(event.target.value)} className="mt-2 min-h-24 w-full rounded-xl border border-slate-700 bg-slate-950 p-4" /></label><div className="mt-5 grid gap-3 md:grid-cols-2">{models.map((model) => <button type="button" key={model.model_id} onClick={() => setModelId(model.model_id)} className={`rounded-xl border p-4 text-left ${modelId === model.model_id ? "border-fuchsia-400 bg-fuchsia-500/10" : "border-slate-700 bg-slate-950"}`}><div className="flex items-start justify-between gap-3"><div className="font-semibold">{model.name}</div><span className={`text-xs font-bold ${model.availability === "ready" ? "text-lime-300" : "text-amber-300"}`}>{model.availability === "ready" ? "Ready" : "Architecture ready"}</span></div><div className="mt-2 text-xs text-slate-400">{model.provider} · {model.gpu_required ? "GPU needed only for real inference" : "Runs on CPU"}</div></button>)}</div></section>

    <div className="mt-6 grid gap-6 lg:grid-cols-2"><section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-cyan-300">2 · How to use the model</div><div className="mt-4 space-y-3">{([{ key: "architecture", title: "Architecture mode", body: "Use the model interface to define the product. No surrogate inference or GPU required." }, { key: "validated", title: "Validated mode", body: "Run the physics model and use real results to refine the architecture." }] as const).map((item) => <button type="button" key={item.key} disabled={item.key === "validated" && !validatedAvailable} onClick={() => setExecutionMode(item.key)} className={`w-full rounded-xl border p-4 text-left disabled:cursor-not-allowed disabled:opacity-40 ${executionMode === item.key ? "border-cyan-400 bg-cyan-500/10" : "border-slate-700"}`}><div className="font-semibold">{item.title}</div><div className="mt-1 text-xs text-slate-400">{item.body}</div>{item.key === "validated" && !validatedAvailable && <div className="mt-2 text-xs font-semibold text-amber-300">Connect NIM or a GPU worker to enable</div>}</button>)}</div></section>
      <section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-violet-300">3 · Agent model</div><div className="mt-4 flex gap-3">{(["standard", "smart"] as const).map((item) => <button type="button" key={item} onClick={() => setAgentMode(item)} className={`rounded-lg border px-4 py-2 capitalize ${agentMode === item ? "border-violet-400 bg-violet-500/10" : "border-slate-700"}`}>{item}</button>)}</div>{agentMode === "standard" && <select value={standardModel} onChange={(event) => setStandardModel(event.target.value)} className="mt-4 w-full rounded-lg border border-slate-700 bg-slate-950 p-3"><option value="chiploop_default">ChipLoop default model</option><option value="nvidia_nemotron">NVIDIA Nemotron for every agent</option></select>}<p className="mt-4 text-xs text-slate-400">Smart mode selects the model for each agent. The chosen policy is saved with the run.</p></section></div>

    <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-lime-300">4 · Choose where the design goes</div><div className="mt-4 grid gap-3 md:grid-cols-2 xl:grid-cols-4">{paths.map((path) => <button type="button" key={path.key} onClick={() => setImplementationPath(path.key)} className={`rounded-xl border p-4 text-left ${implementationPath === path.key ? "border-lime-400 bg-lime-500/10" : "border-slate-700 bg-slate-950"}`}><div className="font-semibold">{path.title}</div><div className="mt-2 text-xs leading-5 text-slate-400">{path.body}</div></button>)}</div><div className="mt-6 overflow-x-auto"><div className="flex min-w-max items-center gap-2">{stages.map((stage, index) => <div key={stage} className="contents"><div className="w-36 rounded-xl border border-slate-700 bg-slate-950 p-3 text-center text-sm"><span className="mr-2 text-fuchsia-300">{index + 1}</span>{stage}</div>{index < stages.length - 1 && <span className="text-slate-500">→</span>}</div>)}</div></div></section>

    {implementationPath !== "architecture_only" && <section className="mt-6 rounded-2xl border border-cyan-900/60 bg-cyan-950/15 p-6"><HemAutomaticRunControls enabled={hemEnabled} adaptive={hemAdaptive} onEnabledChange={setHemEnabled} onAdaptiveChange={setHemAdaptive} currentStageLabel="Physical AI architecture" nextStageLabel="RTL generation" /><p className="mt-4 text-sm text-slate-400">When enabled, ChipLoop continues automatically through the selected path. When disabled, the completed dashboard shows the next workflow button.</p></section>}
    {error && <div className="mt-5 rounded-xl border border-red-500/30 bg-red-500/10 p-4 text-red-200">{error}</div>}
    <button onClick={start} disabled={!token || !selected || running} className="mt-6 w-full rounded-xl bg-fuchsia-400 px-6 py-4 text-lg font-bold text-slate-950 disabled:opacity-50">{running ? "Starting the journey…" : hemEnabled && implementationPath !== "architecture_only" ? "Run the complete journey" : "Run Physical AI agents"}</button>
  </div></main>;
}
