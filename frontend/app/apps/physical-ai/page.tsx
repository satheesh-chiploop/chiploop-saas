"use client";

import { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { HemAutomaticRunControls } from "@/components/HemAutomaticRun";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const supabase = createClientComponentClient();

type PhysicsModel = {
  model_id: string;
  name: string;
  provider: string;
  domain: string;
  runtime: string;
  availability: string;
  gpu_required: boolean;
};

export default function PhysicalAiStudioPage() {
  const router = useRouter();
  const [token, setToken] = useState<string | null>(null);
  const [models, setModels] = useState<PhysicsModel[]>([]);
  const [modelId, setModelId] = useState("chiploop.pmsm.dq.v1");
  const [objective, setObjective] = useState("Validate PMSM speed control and prepare an FPGA implementation handoff");
  const [target, setTarget] = useState("fpga");
  const [mode, setMode] = useState<"standard" | "smart">("standard");
  const [standardModel, setStandardModel] = useState("chiploop_default");
  const [voltage, setVoltage] = useState("48");
  const [speed, setSpeed] = useState("3000");
  const [load, setLoad] = useState("0.15");
  const [running, setRunning] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [hemEnabled, setHemEnabled] = useState(true);
  const [hemAdaptive, setHemAdaptive] = useState(false);
  const [hemStages, setHemStages] = useState({ fpga_exploration: true, fpga_bitstream: true, firmware_product: true });

  useEffect(() => {
    supabase.auth.getSession().then(async ({ data }) => {
      if (!data.session) return router.replace("/login?next=/apps/physical-ai");
      const accessToken = data.session.access_token;
      setToken(accessToken);
      const rerun = window.localStorage.getItem("chiploop_physical_ai_rerun");
      if (rerun) {
        try {
          const prior = JSON.parse(rerun);
          const requirements = prior.requirements || {};
          const parameters = requirements.parameters || {};
          if (requirements.objective) setObjective(String(requirements.objective));
          if (requirements.implementation_target) setTarget(String(requirements.implementation_target));
          if (prior.physics_model_id) setModelId(String(prior.physics_model_id));
          if (parameters.dc_bus_voltage_v != null) setVoltage(String(parameters.dc_bus_voltage_v));
          if (parameters.rated_speed_rpm != null) setSpeed(String(parameters.rated_speed_rpm));
          if (parameters.load_torque_nm != null) setLoad(String(parameters.load_torque_nm));
        } finally {
          window.localStorage.removeItem("chiploop_physical_ai_rerun");
        }
      }
      const response = await fetch(`${API_BASE}/apps/physical-ai/models`, { headers: { Authorization: `Bearer ${accessToken}` } });
      if (response.ok) setModels((await response.json()).models || []);
    });
  }, [router]);

  const selected = models.find((model) => model.model_id === modelId);

  async function start() {
    if (!token || running || selected?.availability !== "ready") return;
    setRunning(true);
    setError(null);
    try {
      const response = await fetch(`${API_BASE}/apps/physical-ai/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", Authorization: `Bearer ${token}` },
        body: JSON.stringify({
          application: "pmsm_motor_control",
          objective,
          physics_domain: selected?.domain || "motor_control",
          physics_model_id: modelId,
          implementation_target: target,
          maximum_error_percent: 3,
          operating_envelope: { speed_rpm: [0, Number(speed)], load_torque_nm: [0, Number(load)] },
          safety_constraints: ["current limit must pass", "winding temperature below 120 C"],
          parameters: { dc_bus_voltage_v: Number(voltage), rated_speed_rpm: Number(speed), load_torque_nm: Number(load), control_loop_hz: 20000 },
          model_policy: { mode, selected_model: standardModel },
          hem_enabled: hemEnabled,
          hem_mode: hemAdaptive ? "adaptive" : "fixed",
          hem_goal: "product_demo",
          hem_stage_toggles: hemStages,
        }),
      });
      const data = await response.json();
      if (!response.ok) throw new Error(data.detail || "Unable to start Physical AI workflow");
      router.push(data.dashboard_path);
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e));
      setRunning(false);
    }
  }

  return <main className="min-h-screen bg-slate-950 text-white">
    <div className="mx-auto max-w-6xl px-6 py-10">
      <div className="flex items-center justify-between"><button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Back to Apps</button><span className="rounded-full bg-violet-500/15 px-3 py-1 text-sm text-violet-200">Parent workflow</span></div>
      <h1 className="mt-8 text-4xl font-extrabold">Physical AI Design Studio</h1>
      <p className="mt-3 max-w-4xl text-slate-300">Define an application, select its physics model, validate the operating envelope, then hand approved evidence to ChipLoop’s existing architecture, digital, FPGA, firmware, and product loops.</p>

      <div className="mt-8 grid gap-6 lg:grid-cols-2">
        <section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6">
          <h2 className="text-xl font-bold">1. Application requirements</h2>
          <label className="mt-4 block text-sm text-slate-300">Objective<textarea value={objective} onChange={(e) => setObjective(e.target.value)} className="mt-2 min-h-24 w-full rounded-lg border border-slate-700 bg-slate-950 p-3" /></label>
          <div className="mt-4 grid grid-cols-3 gap-3">
            {[['DC bus (V)', voltage, setVoltage], ['Speed (RPM)', speed, setSpeed], ['Load (N·m)', load, setLoad]].map(([label, value, setter]) => <label key={label as string} className="text-sm text-slate-300">{label as string}<input type="number" step="any" value={value as string} onChange={(e) => (setter as (value: string) => void)(e.target.value)} className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 p-3" /></label>)}
          </div>
          <label className="mt-4 block text-sm text-slate-300">Implementation target<select value={target} onChange={(e) => setTarget(e.target.value)} className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 p-3"><option value="fpga">FPGA</option><option value="asic">ASIC</option><option value="software">Software</option></select></label>
        </section>

        <section className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6">
          <h2 className="text-xl font-bold">2. Physics model</h2>
          <div className="mt-4 space-y-3">{models.map((model) => <button key={model.model_id} onClick={() => setModelId(model.model_id)} className={`w-full rounded-xl border p-4 text-left ${modelId === model.model_id ? "border-violet-400 bg-violet-500/15" : "border-slate-700"}`}><div className="flex justify-between gap-3"><span className="font-semibold">{model.name}</span><span className={model.availability === "ready" ? "text-lime-300" : "text-amber-300"}>{model.availability.replaceAll("_", " ")}</span></div><div className="mt-1 text-xs text-slate-400">{model.provider} · {model.runtime} · {model.gpu_required ? "GPU" : "CPU"}</div></button>)}</div>
          <h3 className="mt-6 font-semibold">Agent model policy</h3>
          <div className="mt-3 flex gap-3">{(["standard", "smart"] as const).map((item) => <button key={item} onClick={() => setMode(item)} className={`rounded-lg border px-4 py-2 capitalize ${mode === item ? "border-violet-400 bg-violet-500/15" : "border-slate-700"}`}>{item}</button>)}</div>
          {mode === "standard" && <select value={standardModel} onChange={(e) => setStandardModel(e.target.value)} className="mt-3 w-full rounded-lg border border-slate-700 bg-slate-950 p-3"><option value="chiploop_default">ChipLoop Default</option><option value="nvidia_nemotron">NVIDIA Nemotron</option></select>}
        </section>
      </div>

      <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/40 p-6"><h2 className="text-xl font-bold">3. HEM end-to-end automation</h2><div className="mt-4"><HemAutomaticRunControls enabled={hemEnabled} adaptive={hemAdaptive} onEnabledChange={setHemEnabled} onAdaptiveChange={setHemAdaptive} currentStageLabel="Physical AI RTL validation" nextStageLabel="FPGA Target Explorer" stageOptions={[{ key: "fpga_exploration", label: "FPGA Target Explorer", enabled: hemStages.fpga_exploration }, { key: "fpga_bitstream", label: "FPGA RTL to Bitstream", enabled: hemStages.fpga_bitstream }, { key: "firmware_product", label: "Firmware, validation + product demo", enabled: hemStages.firmware_product }]} onStageToggle={(key, value) => setHemStages((current) => ({ ...current, [key]: value }))} /></div><div className="mt-4 grid gap-3 md:grid-cols-3 xl:grid-cols-6">{["Physics + fixed point", "RTL compile + smoke", "FPGA exploration", "FPGA bitstream", "Firmware + software", "Validation + product demo"].map((stage, index) => <div key={stage} className="rounded-lg bg-slate-950 p-3 text-sm"><span className="mr-2 text-violet-300">{index + 1}</span>{stage}</div>)}</div><p className="mt-4 text-xs text-amber-200">Board programming and motor energization always require explicit hardware approval.</p>{error && <p className="mt-4 text-red-300">{error}</p>}<button onClick={start} disabled={!token || running || selected?.availability !== "ready"} className="mt-6 rounded-xl bg-violet-400 px-6 py-3 font-bold text-slate-950 disabled:opacity-50">{running ? "Starting Physical AI loop…" : hemEnabled ? "Start automatic Physical AI loop" : "Run Physical AI validation only"}</button></section>
    </div>
  </main>;
}
