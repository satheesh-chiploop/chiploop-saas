"use client";

import { useEffect, useMemo, useState } from "react";
import { useParams, useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import { HemChildDashboardLinks } from "@/components/HemAutomaticRun";

const API_BASE = process.env.NEXT_PUBLIC_API_URL || "/api";
const supabase = createClientComponentClient();

type SweepCase = {
  target_speed_rpm: number;
  load_torque_nm: number;
  final_speed_rpm: number;
  speed_error_percent: number;
  maximum_current_a: number;
  voltage_saturation_percent: number;
  feasible: boolean;
};

type ResultPayload = {
  status: string;
  requirements: { objective: string; accuracy: { maximum_error_percent: number }; parameters: Record<string, number>; implementation_target: string };
  physics_model: { name: string; model_id: string; runtime: string };
  physics_execution: {
    execution_mode?: string;
    implementation_path?: "architecture_only" | "digital_ip_asic" | "fpga_prototype" | "fpga_then_asic";
    inference_status?: string;
    interface?: { checkpoint: string; reference_url: string; inputs: string[]; outputs: string[]; inference: { status: string; reason: string } };
    architecture?: { execution_partition?: Record<string, string>; data_flow?: string[]; trust_boundaries?: string[]; product_name?: string; product_summary?: string; blocks?: string[] };
    digital_ip_spec?: { name: string; purpose: string; interfaces: string[]; blocks: string[]; requirements: string[]; downstream_loop: string };
    validation?: { architecture_gate: string; surrogate_inference_gate: string; required_before_validated_mode: string[]; digital_ip_tests: string[] };
    product_map?: { product: string; milestones: Array<{ id: string; name: string; status: string }> };
    metrics: Record<string, number | string | boolean | Record<string, boolean>>;
    operating_sweep: { cases: SweepCase[]; feasible_cases: number; total_cases: number };
    fixed_point: {
      status: string;
      passed: boolean;
      word_bits: number;
      total_overflow_count: number;
      acceptance: { maximum_range_normalized_error_percent: number };
      formats: Record<string, { q_format: string; resolution: number; minimum: number; maximum: number }>;
      signal_metrics: Record<string, { maximum_range_normalized_error_percent: number; overflow_count: number; passed: boolean }>;
    };
    rtl: {
      status: string;
      top_module: string;
      sources: string[];
      verification: { tool: string; available: boolean; compiled: boolean; smoke_passed: boolean; compile_stderr?: string; run_stdout?: string };
      limitations: string[];
    };
  };
  loop: { physics_passed: boolean; fixed_point_passed: boolean; rtl_smoke_passed: boolean; stages: Array<{ id: string; owner: string; status: string; app_path?: string }> };
  hem: { enabled: boolean; mode: string; goal: string; stage_toggles: Record<string, boolean>; start_condition: string };
  files: Record<string, string>;
};

const plotTitles: Record<string, string> = {
  speed_response_plot: "Speed response",
  current_response_plot: "q-axis current",
  operating_envelope_plot: "Operating envelope",
};

export default function PhysicalAiResultsPage() {
  const { workflowId } = useParams<{ workflowId: string }>();
  const router = useRouter();
  const [result, setResult] = useState<ResultPayload | null>(null);
  const [plots, setPlots] = useState<Record<string, string>>({});
  const [phase, setPhase] = useState("queued");
  const [error, setError] = useState<string | null>(null);
  const [logs, setLogs] = useState("");

  useEffect(() => {
    let stopped = false;
    let timer: ReturnType<typeof setTimeout> | undefined;
    async function poll() {
      const { data } = await supabase.auth.getSession();
      if (!data.session) return router.replace(`/login?next=/apps/physical-ai/results/${workflowId}`);
      try {
        const response = await fetch(`${API_BASE}/apps/physical-ai/${workflowId}/result`, { headers: { Authorization: `Bearer ${data.session.access_token}` }, cache: "no-store" });
        const payload = await response.json();
        if (response.status === 202) {
          setPhase(payload.phase || payload.status || "running");
          setLogs(payload.logs || "");
          if (!stopped) timer = setTimeout(poll, 1500);
          return;
        }
        if (!response.ok) throw new Error(payload.detail || payload.logs || "Unable to load Physical AI result");
        if (!stopped) {
          setResult(payload.result);
          setPlots(payload.plots || {});
          setPhase(payload.phase || "completed");
          setLogs(payload.logs || "");
          const hemTerminal = ["hem_complete", "hem_failed", "done", "needs_revision"].includes(String(payload.phase || "").toLowerCase());
          if (payload.result?.hem?.enabled && !hemTerminal) timer = setTimeout(poll, 2500);
        }
      } catch (e) {
        if (!stopped) setError(e instanceof Error ? e.message : String(e));
      }
    }
    poll();
    return () => { stopped = true; if (timer) clearTimeout(timer); };
  }, [router, workflowId]);

  const failedCases = useMemo(() => result?.physics_execution.operating_sweep?.cases.filter((item) => !item.feasible) || [], [result]);

  function revise() {
    if (result) window.localStorage.setItem("chiploop_physical_ai_rerun", JSON.stringify({ requirements: result.requirements, physics_model_id: result.physics_model.model_id }));
    router.push("/apps/physical-ai?revise=1");
  }

  if (!result) return <main className="min-h-screen bg-slate-950 px-6 py-12 text-white"><div className="mx-auto max-w-5xl"><div className="flex flex-wrap items-end justify-between gap-3"><div><div className="text-xs font-bold uppercase tracking-widest text-violet-300">Physical AI Loop</div><h1 className="mt-3 text-3xl font-bold">Journey is running</h1><p className="mt-2 text-slate-400">This page stays open while agents execute.</p></div><span className="rounded-full bg-cyan-500/15 px-3 py-2 text-xs font-bold uppercase text-cyan-200">{phase.replaceAll("_", " ")}</span></div><section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Running log</h2><pre className="mt-4 max-h-[32rem] overflow-auto whitespace-pre-wrap rounded-xl bg-slate-950 p-4 text-xs leading-6 text-slate-300">{logs || "Waiting for the first agent…"}</pre></section>{error && <p className="mt-5 text-red-300">{error}</p>}</div></main>;

  if (result.physics_execution.execution_mode === "architecture") {
    const execution = result.physics_execution;
    const modelInterface = execution.interface!;
    const architecture = execution.architecture!;
    const digitalIp = execution.digital_ip_spec!;
    const validation = execution.validation!;
    const executionPartition = architecture?.execution_partition || { product: architecture?.product_summary || "Product architecture generated", digital_ip: "RTL-ready digital IP specification generated", implementation: "Selected FPGA or ASIC path" };
    const stopAfterArchitecture = execution.implementation_path === "architecture_only";
    const pathLabel = ({ architecture_only: "Architecture only", digital_ip_asic: "Digital IP / ASIC", fpga_prototype: "FPGA prototype", fpga_then_asic: "FPGA then ASIC" } as Record<string, string>)[execution.implementation_path || "digital_ip_asic"];
    return <main className="min-h-screen bg-slate-950 text-white"><div className="mx-auto max-w-7xl px-6 py-10">
      <div className="flex flex-wrap items-center justify-between gap-3"><button onClick={() => router.push("/apps/physical-ai")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Physical AI Studio</button><div className="flex gap-3"><button onClick={() => window.open(`/dashboard/${workflowId}?stage=physical_ai&app=PhysicalAI`, "_blank", "noopener,noreferrer")} className="rounded-lg border border-cyan-400 px-4 py-2 text-sm text-cyan-200">Open Dashboard ↗</button><a href={`/api/workflow/${encodeURIComponent(workflowId)}/download_zip?full=1`} className="rounded-lg bg-violet-400 px-4 py-2 text-sm font-bold text-slate-950">Download artifacts</a></div></div>
      <div className="mt-8 flex flex-wrap items-end justify-between gap-4"><div><div className="text-xs font-bold uppercase tracking-widest text-cyan-300">Pretrained-surrogate reference journey</div><h1 className="mt-2 text-4xl font-extrabold">Architecture and digital-IP definition</h1><p className="mt-3 max-w-3xl text-slate-300">{result.requirements.objective}</p><p className="mt-2 text-sm text-violet-200">Selected implementation: {pathLabel}</p></div><span className="rounded-full bg-lime-500/15 px-4 py-2 text-sm font-bold text-lime-200">{stopAfterArchitecture ? "Architecture complete" : "Ready for Digital Design"}</span></div>
      <section className="mt-8 rounded-2xl border border-amber-500/30 bg-amber-500/10 p-5"><div className="font-bold text-amber-200">Surrogate inference: not executed</div><p className="mt-2 text-sm text-amber-100">{modelInterface.inference.reason} This run contains no predicted drag, pressure, lift, or flow values.</p></section>
      <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Selected pretrained model</h2><div className="mt-4 grid gap-4 md:grid-cols-3"><div><div className="text-xs uppercase text-slate-500">Model</div><div className="mt-2 font-bold">{result.physics_model.name}</div></div><div><div className="text-xs uppercase text-slate-500">Checkpoint</div><div className="mt-2 font-mono text-sm text-violet-200">{modelInterface.checkpoint}</div></div><div><div className="text-xs uppercase text-slate-500">Runtime</div><div className="mt-2">GPU/NIM for future inference</div></div></div><a className="mt-5 inline-block text-sm text-cyan-300 underline" href={modelInterface.reference_url} target="_blank" rel="noreferrer">Open NVIDIA model reference</a><div className="mt-5 grid gap-4 md:grid-cols-2"><div><div className="text-sm font-semibold">Published inputs</div><div className="mt-2 flex flex-wrap gap-2">{modelInterface.inputs.map((item) => <span key={item} className="rounded bg-slate-950 px-3 py-2 font-mono text-xs">{item}</span>)}</div></div><div><div className="text-sm font-semibold">Published outputs</div><div className="mt-2 flex flex-wrap gap-2">{modelInterface.outputs.map((item) => <span key={item} className="rounded bg-slate-950 px-3 py-2 font-mono text-xs">{item}</span>)}</div></div></div></section>
      <section className="mt-8 grid gap-6 lg:grid-cols-2"><article className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Product architecture</h2><div className="mt-4 space-y-3">{Object.entries(executionPartition).map(([key, value]) => <div key={key} className="rounded-lg bg-slate-950 p-3"><div className="text-xs uppercase text-slate-500">{key.replaceAll("_", " ")}</div><div className="mt-1 text-sm">{String(value)}</div></div>)}</div></article><article className="rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Digital-IP specification</h2><div className="mt-2 font-mono text-violet-200">{digitalIp?.name || architecture?.product_name || "Physical AI digital IP"}</div><p className="mt-3 text-sm text-slate-300">{digitalIp?.purpose || architecture?.product_summary}</p><div className="mt-4 text-sm font-semibold">Blocks</div><ul className="mt-2 list-disc space-y-1 pl-5 text-sm text-slate-300">{(digitalIp?.blocks || architecture?.blocks || []).map((item) => <li key={item}>{item}</li>)}</ul></article></section>
      <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Execution and gates</h2><pre className="mt-4 max-h-80 overflow-auto whitespace-pre-wrap rounded-xl bg-slate-950 p-4 text-xs leading-6 text-slate-300">{logs || "Execution log is syncing…"}</pre><div className="mt-5 grid gap-3 md:grid-cols-2"><div className="rounded-lg border border-lime-500/30 p-4 text-lime-200">Architecture gate: {validation.architecture_gate}</div><div className="rounded-lg border border-amber-500/30 p-4 text-amber-200">Inference gate: {validation.surrogate_inference_gate.replaceAll("_", " ")}</div></div></section>
      {result.hem.enabled && !stopAfterArchitecture && <section className="mt-8 rounded-2xl border border-cyan-500/30 bg-cyan-500/10 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><div className="text-xs font-bold uppercase text-cyan-300">HEM automatic journey</div><h2 className="mt-2 text-xl font-bold">Following the {pathLabel} path</h2></div><span className="rounded-full bg-slate-950 px-3 py-2 text-xs font-bold uppercase text-cyan-200">{phase.replaceAll("_", " ")}</span></div><p className="mt-3 text-sm text-slate-300">RTL generation and verification run first. FPGA paths then explore and select a board before bitstream generation; ASIC paths continue to Arch2Tapeout.</p><HemChildDashboardLinks logs={logs} /></section>}
      {stopAfterArchitecture ? <section className="mt-8 rounded-2xl border border-slate-700 bg-slate-900/50 p-6"><div className="text-xs font-bold uppercase text-slate-400">Journey complete</div><h2 className="mt-2 text-xl font-bold">Stopped after architecture</h2><p className="mt-2 text-sm text-slate-300">No RTL, verification, FPGA, or ASIC implementation was requested.</p></section> : !result.hem.enabled && <section className="mt-8 rounded-2xl border border-lime-500/30 bg-lime-500/10 p-6"><div className="text-xs font-bold uppercase text-lime-300">Next workflow available</div><h2 className="mt-2 text-xl font-bold">RTL generation</h2><p className="mt-2 text-sm text-slate-300">HEM is off. Continue manually to generate and verify RTL, then follow the selected {pathLabel} implementation path.</p><button onClick={() => router.push(`/apps/arch2rtl?handoff=1&from_workflow_id=${encodeURIComponent(workflowId)}&implementation_path=${encodeURIComponent(execution.implementation_path || "digital_ip_asic")}`)} className="mt-4 rounded-xl bg-lime-300 px-5 py-3 text-sm font-bold text-slate-950">Open RTL generation</button></section>}
      <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/40 p-6"><h2 className="text-xl font-bold">Reference-journey stages</h2><div className="mt-4 grid gap-3 md:grid-cols-3">{result.loop.stages.map((stage) => <div key={stage.id} className="rounded-xl bg-slate-950 p-4"><div className="text-sm font-semibold capitalize">{stage.id.replaceAll("_", " ")}</div><div className={`mt-2 text-xs uppercase ${stage.status === "completed" || stage.status === "ready" ? "text-lime-300" : "text-amber-300"}`}>{stage.status.replaceAll("_", " ")}</div></div>)}</div></section>
    </div></main>;
  }

  const metrics = result.physics_execution.metrics;
  const sweep = result.physics_execution.operating_sweep;
  const gatesPassed = result.loop.physics_passed && result.loop.fixed_point_passed && result.loop.rtl_smoke_passed;
  return <main className="min-h-screen bg-slate-950 text-white"><div className="mx-auto max-w-7xl px-6 py-10">
    <div className="flex flex-wrap items-center justify-between gap-3"><button onClick={() => router.push("/apps/physical-ai")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm">Physical AI Studio</button><div className="flex flex-wrap gap-3"><button onClick={() => window.open(`/dashboard/${workflowId}?stage=physical_ai&app=PhysicalAI`, "_blank", "noopener,noreferrer")} className="rounded-lg border border-cyan-400 px-4 py-2 text-sm text-cyan-200">Open Dashboard ↗</button><button onClick={revise} className="rounded-lg border border-violet-400 px-4 py-2 text-sm text-violet-200">Revise and rerun</button><a href={`/api/workflow/${encodeURIComponent(workflowId)}/download_zip?full=1`} className="rounded-lg bg-violet-400 px-4 py-2 text-sm font-bold text-slate-950">Download artifacts</a></div></div>
    <div className="mt-8 flex flex-wrap items-end justify-between gap-4"><div><div className="text-xs font-bold uppercase tracking-widest text-violet-300">Motor reference journey</div><h1 className="mt-2 text-4xl font-extrabold">PMSM equation results</h1><p className="mt-3 max-w-3xl text-slate-300">{result.requirements.objective}</p></div><span className={`rounded-full px-4 py-2 text-sm font-bold ${result.loop.physics_passed && result.loop.fixed_point_passed && result.loop.rtl_smoke_passed ? "bg-lime-500/15 text-lime-200" : "bg-amber-500/15 text-amber-200"}`}>{result.loop.physics_passed && result.loop.fixed_point_passed && result.loop.rtl_smoke_passed ? "Ready for FPGA exploration" : "Revision required"}</span></div>

    <section className="mt-8 grid gap-4 sm:grid-cols-2 lg:grid-cols-5">{[
      ["Target speed", `${Number(metrics.target_speed_rpm).toFixed(0)} RPM`], ["Final speed", `${Number(metrics.final_speed_rpm).toFixed(1)} RPM`], ["Speed error", `${Number(metrics.steady_state_speed_error_percent).toFixed(2)}%`], ["Maximum current", `${Number(metrics.maximum_current_a).toFixed(2)} A`], ["Sweep passed", `${sweep.feasible_cases}/${sweep.total_cases}`],
    ].map(([label, value]) => <div key={label} className="rounded-xl border border-slate-800 bg-slate-900/60 p-4"><div className="text-xs uppercase text-slate-500">{label}</div><div className="mt-2 text-xl font-bold">{value}</div></div>)}</section>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><h2 className="text-xl font-bold">Running log</h2><p className="mt-2 text-sm text-slate-400">Execution state is persisted in this workflow&apos;s Supabase logs.</p></div><span className="rounded-full bg-lime-500/15 px-3 py-2 text-sm font-bold text-lime-200">Physical AI complete</span></div><pre className="mt-4 max-h-80 overflow-auto whitespace-pre-wrap rounded-xl bg-slate-950 p-4 text-xs leading-6 text-slate-300">{logs || "Execution log is syncing…"}</pre></section>

    <section className="mt-8 grid gap-6 lg:grid-cols-2">{Object.entries(plots).map(([key, svg]) => <article key={key} className={`overflow-hidden rounded-2xl border border-slate-800 bg-slate-900/40 p-4 ${key === "operating_envelope_plot" ? "lg:col-span-2" : ""}`}><h2 className="mb-3 text-lg font-bold">{plotTitles[key] || key}</h2><div className="overflow-x-auto [&_svg]:h-auto [&_svg]:max-w-full" dangerouslySetInnerHTML={{ __html: svg }} /></article>)}</section>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><h2 className="text-xl font-bold">Fixed-point validation</h2><p className="mt-2 text-sm text-slate-400">{result.physics_execution.fixed_point.word_bits}-bit signal formats · maximum allowed normalized error {result.physics_execution.fixed_point.acceptance.maximum_range_normalized_error_percent}%</p></div><span className={`rounded-full px-3 py-2 text-sm font-bold ${result.physics_execution.fixed_point.passed ? "bg-lime-500/15 text-lime-200" : "bg-red-500/15 text-red-200"}`}>{result.physics_execution.fixed_point.passed ? "Passed" : "Failed"} · {result.physics_execution.fixed_point.total_overflow_count} overflows</span></div><div className="mt-5 overflow-x-auto"><table className="w-full min-w-[720px] text-left text-sm"><thead className="text-slate-400"><tr>{["Signal", "Q format", "Resolution", "Range", "Max error", "Overflow", "Status"].map((item) => <th key={item} className="border-b border-slate-700 p-3">{item}</th>)}</tr></thead><tbody>{Object.entries(result.physics_execution.fixed_point.formats).map(([signal, format]) => { const metric = result.physics_execution.fixed_point.signal_metrics[signal]; return <tr key={signal}><td className="p-3">{signal}</td><td className="p-3 font-mono text-violet-200">{format.q_format}</td><td className="p-3">{format.resolution.toPrecision(4)}</td><td className="p-3">{format.minimum.toFixed(2)} to {format.maximum.toFixed(2)}</td><td className="p-3">{metric.maximum_range_normalized_error_percent.toFixed(4)}%</td><td className="p-3">{metric.overflow_count}</td><td className={`p-3 ${metric.passed ? "text-lime-300" : "text-red-300"}`}>{metric.passed ? "Pass" : "Fail"}</td></tr>; })}</tbody></table></div><p className="mt-4 text-xs text-amber-200">This gate validates quantized reference I/O vectors. Arithmetic-stage bit growth will be checked again against generated RTL.</p></section>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><h2 className="text-xl font-bold">Motor-control RTL package</h2><p className="mt-2 text-sm text-slate-400">Top module: <span className="font-mono text-violet-200">{result.physics_execution.rtl.top_module}</span> · {result.physics_execution.rtl.sources.length} synthesizable source files</p></div><span className={`rounded-full px-3 py-2 text-sm font-bold ${result.physics_execution.rtl.verification.smoke_passed ? "bg-lime-500/15 text-lime-200" : "bg-red-500/15 text-red-200"}`}>{result.physics_execution.rtl.verification.smoke_passed ? "Compile + smoke passed" : "Needs verification"}</span></div><div className="mt-5 grid gap-3 md:grid-cols-4">{[["Compiler", result.physics_execution.rtl.verification.tool], ["Tool available", result.physics_execution.rtl.verification.available ? "Yes" : "No"], ["Compiled", result.physics_execution.rtl.verification.compiled ? "Pass" : "Fail"], ["Smoke test", result.physics_execution.rtl.verification.smoke_passed ? "Pass" : "Fail"]].map(([label, value]) => <div key={label} className="rounded-xl bg-slate-950 p-4"><div className="text-xs uppercase text-slate-500">{label}</div><div className="mt-2 font-bold">{value}</div></div>)}</div><div className="mt-5 flex flex-wrap gap-2">{result.physics_execution.rtl.sources.map((source) => <span key={source} className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 font-mono text-xs text-slate-300">{source}</span>)}</div><div className="mt-5 rounded-xl border border-amber-500/25 bg-amber-500/10 p-4 text-sm text-amber-100"><div className="font-semibold">Hardware gate still required</div><ul className="mt-2 list-disc space-y-1 pl-5">{result.physics_execution.rtl.limitations.map((item) => <li key={item}>{item}</li>)}</ul></div></section>

    <section className="mt-8 rounded-2xl border border-cyan-900/60 bg-cyan-950/15 p-6"><div className="flex flex-wrap items-center justify-between gap-3"><div><h2 className="text-xl font-bold">HEM Automatic Run</h2><p className="mt-2 text-sm text-slate-400">Goal: {result.hem.goal.replaceAll("_", " ")} · policy: {result.hem.mode} · starts only after {result.hem.start_condition.replaceAll("_", " ")}</p></div><span className={`rounded-full px-3 py-2 text-sm font-bold ${phase === "hem_complete" ? "bg-lime-500/15 text-lime-200" : phase === "hem_failed" ? "bg-red-500/15 text-red-200" : result.hem.enabled ? "bg-cyan-500/15 text-cyan-200" : "bg-slate-700 text-slate-300"}`}>{result.hem.enabled ? phase.replaceAll("_", " ") : "Disabled"}</span></div><div className="mt-4 grid gap-3 sm:grid-cols-2">{Object.entries(result.hem.stage_toggles).map(([stage, enabled]) => <div key={stage} className="rounded-lg border border-slate-800 bg-slate-950 p-3 text-sm"><span className={enabled ? "text-lime-300" : "text-slate-500"}>{enabled ? "Enabled" : "Skipped"}</span><span className="ml-2 capitalize text-slate-200">{stage.replaceAll("_", " ")}</span></div>)}</div><HemChildDashboardLinks logs={logs} /></section>

    {gatesPassed && !result.hem.enabled ? <section className="mt-8 rounded-2xl border border-lime-500/30 bg-lime-500/10 p-6"><div className="flex flex-col justify-between gap-4 sm:flex-row sm:items-center"><div><div className="text-xs font-bold uppercase tracking-wide text-lime-300">Passed — next workflow available</div><h2 className="mt-2 text-xl font-bold">RTL generation</h2><p className="mt-2 max-w-3xl text-sm text-slate-300">HEM is off. Continue manually to Arch2RTL, then Verification, followed by the selected FPGA or ASIC path.</p></div><button onClick={() => router.push(`/apps/arch2rtl?handoff=1&from_workflow_id=${encodeURIComponent(workflowId)}`)} className="shrink-0 rounded-xl bg-lime-300 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-lime-200">Open RTL generation</button></div></section> : !gatesPassed ? <section className="mt-8 rounded-2xl border border-amber-500/30 bg-amber-500/10 p-6"><div className="text-xs font-bold uppercase tracking-wide text-amber-300">Next workflow blocked</div><p className="mt-2 text-sm text-amber-100">Revise and rerun until physics, fixed-point, and RTL smoke validation pass.</p></section> : null}

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/50 p-6"><h2 className="text-xl font-bold">Operating-point review</h2>{failedCases.length === 0 ? <p className="mt-3 text-lime-200">Every tested operating point passed.</p> : <><p className="mt-3 text-amber-200">{failedCases.length} operating point{failedCases.length === 1 ? "" : "s"} failed the {result.requirements.accuracy.maximum_error_percent}% speed-error or safety requirement.</p><div className="mt-4 overflow-x-auto"><table className="w-full min-w-[720px] text-left text-sm"><thead className="text-slate-400"><tr>{["Target", "Load", "Achieved", "Error", "Max current", "Voltage saturation", "Likely action"].map((item) => <th key={item} className="border-b border-slate-700 p-3">{item}</th>)}</tr></thead><tbody>{failedCases.map((item) => <tr key={`${item.target_speed_rpm}-${item.load_torque_nm}`} className="text-slate-200"><td className="p-3">{item.target_speed_rpm.toFixed(0)} RPM</td><td className="p-3">{item.load_torque_nm.toFixed(3)} N·m</td><td className="p-3">{item.final_speed_rpm.toFixed(0)} RPM</td><td className="p-3">{item.speed_error_percent.toFixed(2)}%</td><td className="p-3">{item.maximum_current_a.toFixed(2)} A</td><td className="p-3">{item.voltage_saturation_percent.toFixed(1)}%</td><td className="p-3 text-amber-200">{item.voltage_saturation_percent > 50 ? "Raise DC bus, lower speed, or add field weakening" : "Review current limit and controller tuning"}</td></tr>)}</tbody></table></div></>}</section>

    <section className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/40 p-6"><h2 className="text-xl font-bold">Reference-journey stages</h2><div className="mt-4 grid gap-3 md:grid-cols-3">{result.loop.stages.map((stage) => <div key={stage.id} className="rounded-xl border border-slate-800 bg-slate-950 p-4"><div className="text-sm font-semibold capitalize">{stage.id.replaceAll("_", " ")}</div><div className={`mt-2 text-xs uppercase ${stage.status === "completed" || stage.status === "ready" ? "text-lime-300" : "text-amber-300"}`}>{stage.status.replaceAll("_", " ")}</div><div className="mt-1 text-xs text-slate-500">{stage.owner === "existing_loop" ? "Existing ChipLoop loop" : "Physical AI parent"}</div></div>)}</div><p className="mt-5 text-sm text-slate-400">Automatic FPGA Exploration is the next gated milestone. The Coming soon badge remains until implementation, bitstream, firmware, and board validation are tested.</p></section>
  </div></main>;
}
