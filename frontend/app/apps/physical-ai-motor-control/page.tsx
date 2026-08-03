"use client";

import { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const supabase = createClientComponentClient();

type Mode = "standard" | "smart";
type StandardModel = "chiploop_default" | "nvidia_nemotron";

export default function PhysicalAiMotorControlPage() {
  const router = useRouter();
  const [token, setToken] = useState<string | null>(null);
  const [mode, setMode] = useState<Mode>("standard");
  const [standardModel, setStandardModel] = useState<StandardModel>("chiploop_default");
  const [running, setRunning] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [dcBus, setDcBus] = useState("48");
  const [speed, setSpeed] = useState("3000");
  const [loopRate, setLoopRate] = useState("20000");
  const [loadTorque, setLoadTorque] = useState("0.15");

  useEffect(() => {
    supabase.auth.getSession().then(({ data }) => {
      if (!data.session) router.replace("/login?next=/apps/physical-ai-motor-control");
      else setToken(data.session.access_token);
    });
  }, [router]);

  async function start() {
    if (!token || running) return;
    setRunning(true);
    setError(null);
    try {
      const response = await fetch(`${API_BASE}/apps/physical-ai/motor-control/run`, {
        method: "POST",
        headers: { "Content-Type": "application/json", Authorization: `Bearer ${token}` },
        body: JSON.stringify({
          model_policy: { mode, selected_model: standardModel },
          board: "orangecrab_ecp5_85f",
          dc_bus_voltage_v: Number(dcBus),
          rated_speed_rpm: Number(speed),
          control_loop_hz: Number(loopRate),
          pole_pairs: 4,
          target_frequency_mhz: 50,
          maximum_surrogate_error_percent: 3,
          simulation_mode: "equation",
          load_torque_nm: Number(loadTorque),
        }),
      });
      const data = await response.json();
      if (!response.ok) throw new Error(data.detail || "Unable to start Physical AI workflow");
      router.push(data.dashboard_path || `/dashboard/${data.workflow_id}?stage=physical_ai`);
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e));
      setRunning(false);
    }
  }

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <div className="mx-auto max-w-5xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Back to Apps</button>
          <span className="rounded-full bg-violet-500/15 px-3 py-1 text-sm text-violet-200">Physical AI v1</span>
        </div>

        <h1 className="mt-8 text-4xl font-extrabold">Motor Control + Fault Detection</h1>
        <p className="mt-3 max-w-3xl text-slate-300">Run a deterministic PMSM equation model, capture a verified baseline, and prepare the OrangeCrab FPGA handoff. A GPU surrogate can later use the same physics interface.</p>

        <section className="mt-8 grid gap-6 lg:grid-cols-2">
          <div className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6">
            <h2 className="text-xl font-bold">AI model policy</h2>
            <div className="mt-4 grid grid-cols-2 gap-3">
              {(["standard", "smart"] as Mode[]).map((item) => (
                <button key={item} onClick={() => setMode(item)} className={`rounded-xl border p-4 text-left ${mode === item ? "border-violet-400 bg-violet-500/15" : "border-slate-700"}`}>
                  <div className="font-semibold capitalize">{item}</div>
                  <div className="mt-1 text-xs text-slate-400">{item === "standard" ? "One model for every agent" : "ChipLoop routes each agent"}</div>
                </button>
              ))}
            </div>
            {mode === "standard" && (
              <label className="mt-5 block text-sm text-slate-300">Model
                <select value={standardModel} onChange={(e) => setStandardModel(e.target.value as StandardModel)} className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 p-3">
                  <option value="chiploop_default">ChipLoop Default (current model)</option>
                  <option value="nvidia_nemotron">NVIDIA Nemotron</option>
                </select>
              </label>
            )}
            {mode === "smart" && <p className="mt-5 rounded-lg bg-slate-950 p-3 text-sm text-slate-300">Physics planning routes to Nemotron; RTL and verification begin with ChipLoop Default. Every assignment is recorded.</p>}
          </div>

          <div className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6">
            <h2 className="text-xl font-bold">Motor design contract</h2>
            {[['DC bus voltage (V)', dcBus, setDcBus], ['Rated speed (RPM)', speed, setSpeed], ['Control loop (Hz)', loopRate, setLoopRate]].map(([label, value, setter]) => (
              <label key={label as string} className="mt-4 block text-sm text-slate-300">{label as string}
                <input value={value as string} onChange={(e) => (setter as (v: string) => void)(e.target.value)} type="number" className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 p-3" />
              </label>
            ))}
            <label className="mt-4 block text-sm text-slate-300">Load torque (N·m)
              <input value={loadTorque} onChange={(e) => setLoadTorque(e.target.value)} type="number" step="0.01" className="mt-2 w-full rounded-lg border border-slate-700 bg-slate-950 p-3" />
            </label>
            <div className="mt-4 rounded-lg border border-lime-500/30 bg-lime-500/10 p-3 text-sm text-lime-100">Mode: PMSM dq equations · FPGA target: OrangeCrab ECP5-85F · 50 MHz</div>
          </div>
        </section>

        <section className="mt-6 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="grid gap-3 text-sm md:grid-cols-4">
            {['PMSM equation simulation', 'Plots + operating envelope', 'Nemotron/NAT agent plan', 'OrangeCrab FPGA handoff'].map((item, index) => <div key={item} className="rounded-lg bg-slate-950 p-3"><span className="mr-2 text-violet-300">{index + 1}</span>{item}</div>)}
          </div>
          {error && <p className="mt-4 text-sm text-red-300">{error}</p>}
          <button onClick={start} disabled={!token || running} className="mt-6 rounded-xl bg-violet-400 px-6 py-3 font-bold text-slate-950 disabled:opacity-50">{running ? "Running equations…" : "Run motor equation model"}</button>
        </section>
      </div>
    </main>
  );
}
