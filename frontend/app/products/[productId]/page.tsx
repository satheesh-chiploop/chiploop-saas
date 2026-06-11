"use client";

import { useEffect, useMemo, useState } from "react";
import { useParams, useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";
import { apiGet, apiPatch, apiPost } from "@/lib/apiClient";

type Stage = {
  id: string;
  label: string;
  app: string;
  required?: boolean;
  recommended?: boolean;
  optional?: boolean;
  enabled?: boolean;
  settings?: Record<string, unknown>;
};

type Product = {
  id: string;
  name: string;
  product_type: string;
  starting_point: string;
  description: string;
  status: string;
  stage_config?: {
    source?: string;
    reference_slug?: string;
    stages?: Stage[];
  };
  stage_results?: Record<string, unknown>;
  updated_at?: string;
};

type ProductRun = {
  id: string;
  product_id: string;
  status: string;
  current_stage?: string | null;
  error?: string | null;
  stage_results?: Record<string, unknown>;
  created_at?: string;
  updated_at?: string;
  completed_at?: string | null;
};

type StageRun = {
  id: string;
  stage_id: string;
  stage_label: string;
  app: string;
  status: string;
  workflow_id?: string | null;
  run_id?: string | null;
  error?: string | null;
  started_at?: string | null;
  completed_at?: string | null;
};

type ProductRunWithStages = ProductRun & {
  stage_runs?: StageRun[];
};

const APP_LINKS: Record<string, string> = {
  Digital_Arch2RTL: "/apps/arch2rtl",
  Digital_DQA: "/apps/dqa",
  Digital_Verify: "/apps/verify",
  Digital_Arch2Synthesis: "/apps/arch2synthesis",
  verify_closure_loop: "/apps/verify",
  Embedded_Run: "/apps/embedded-run",
  System_Software: "/apps/system-software",
  System_Software_Validation_L2: "/apps/system-software-validation",
  System_Product_App_Builder: "/apps/system-product-builder",
  System_RTL: "/apps/system-rtl",
  System_DQA: "/apps/system-dqa",
  System_Sim: "/apps/system-sim",
  System_Firmware: "/apps/system-firmware",
  System_PD: "/apps/system-pd",
};

type StageField = {
  key: string;
  label: string;
  type: "text" | "number" | "boolean";
  defaultValue: string | number | boolean;
  required?: boolean;
  helper?: string;
};

type StageSchema = {
  fields: StageField[];
  note?: string;
};

const FALLBACK_STAGE_SCHEMAS: Record<string, StageSchema> = {
  Digital_Arch2RTL: {
    note: "Spec text can be left blank only when the product description is detailed enough to use as the RTL spec.",
    fields: [
      { key: "top_module", label: "Top module", type: "text", defaultValue: "" },
      { key: "spec_text", label: "Spec text", type: "text", defaultValue: "", helper: "Used before product description fallback." },
      { key: "enable_packaging", label: "Generate handoff package", type: "boolean", defaultValue: true },
    ],
  },
  Digital_Verify: {
    fields: [
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 4 },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional, 70% line" },
      { key: "enable_formal", label: "Formal", type: "boolean", defaultValue: false },
    ],
  },
  Digital_Arch2Synthesis: {
    note: "Synthesis uses the generated Arch2RTL handoff as RTL input and runs the synthesis stage directly.",
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130A" },
      { key: "toolchain", label: "Toolchain", type: "text", defaultValue: "openlane2" },
      { key: "target_frequency_mhz", label: "Target frequency MHz", type: "number", defaultValue: 100 },
      { key: "constraints_sdc", label: "Constraints SDC", type: "text", defaultValue: "" },
    ],
  },
  System_RTL: {
    note: "System RTL starts from explicit digital, analog, and SoC specs. Downstream System apps auto-bind to this generated workflow.",
    fields: [
      { key: "digital_spec", label: "Digital spec", type: "text", defaultValue: "", required: true },
      { key: "analog_spec", label: "Analog spec", type: "text", defaultValue: "", required: true },
      { key: "soc_spec", label: "SoC spec", type: "text", defaultValue: "", required: true },
      { key: "enable_spec2rtl", label: "Spec2RTL check", type: "boolean", defaultValue: true },
    ],
  },
  System_Sim: {
    fields: [
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 6 },
      { key: "system_sim_testcases", label: "Testcases", type: "text", defaultValue: "system_smoke_test, integrated_input_sanity" },
      { key: "system_sim_seeds", label: "Seeds", type: "text", defaultValue: "1,2,3,4" },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional" },
      { key: "enable_golden_model", label: "Golden model", type: "boolean", defaultValue: true },
    ],
  },
  System_DQA: {
    note: "System DQA uses the System RTL handoff and does not rerun register-map generation.",
    fields: [
      { key: "run_lint", label: "Run lint", type: "boolean", defaultValue: true },
      { key: "run_cdc", label: "Run CDC", type: "boolean", defaultValue: true },
      { key: "run_reset", label: "Run reset integrity", type: "boolean", defaultValue: true },
    ],
  },
  System_Firmware: {
    note: "Firmware auto-binds the System RTL workflow ID, including register-map and top-level handoff artifacts.",
    fields: [
      { key: "firmware_language", label: "Firmware language", type: "text", defaultValue: "rust" },
      { key: "validate_registers", label: "Validate registers", type: "boolean", defaultValue: true },
      { key: "enable_cosim", label: "Enable firmware co-sim", type: "boolean", defaultValue: true },
    ],
  },
  System_PD: {
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130" },
      { key: "analog_physical_mode", label: "Analog physical mode", type: "text", defaultValue: "blackbox" },
      { key: "run_drc", label: "Run DRC", type: "boolean", defaultValue: true },
      { key: "run_lvs", label: "Run LVS", type: "boolean", defaultValue: true },
    ],
  },
  Embedded_Run: {
    fields: [
      { key: "firmware_language", label: "Firmware language", type: "text", defaultValue: "rust" },
      { key: "enable_cosim", label: "Enable firmware co-sim", type: "boolean", defaultValue: false },
    ],
  },
  verify_closure_loop: {
    fields: [
      { key: "max_iterations", label: "Max iterations", type: "number", defaultValue: 1 },
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 5 },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional, 70% line" },
    ],
  },
  System_Software: {
    fields: [
      { key: "app_names", label: "App names", type: "text", defaultValue: "status_cli, product_service" },
      { key: "target_language", label: "Target language", type: "text", defaultValue: "rust" },
    ],
  },
  System_Software_Validation_L2: {
    fields: [
      { key: "validation_mode", label: "Validation mode", type: "text", defaultValue: "full_co_simulation" },
    ],
  },
  System_Product_App_Builder: {
    fields: [
      { key: "app_type", label: "App type", type: "text", defaultValue: "web_dashboard" },
      { key: "target_runtime", label: "Target runtime", type: "text", defaultValue: "simulated_device" },
    ],
  },
};

const FALLBACK_STAGE_SCHEMA: StageSchema = {
  fields: [{ key: "notes", label: "Notes", type: "text", defaultValue: "" }],
};

function typeLabel(value: string) {
  return value.replace(/_/g, "-").replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function stageKind(stage: Stage) {
  if (stage.required) return "Required";
  if (stage.recommended) return "Recommended";
  if (stage.optional) return "Optional";
  return "Stage";
}

function stageEnabled(stage: Stage) {
  if (stage.required) return true;
  if (stage.optional && stage.enabled === undefined) return false;
  return stage.enabled !== false;
}

function fieldValue(stage: Stage, field: StageField) {
  return stage.settings?.[field.key] ?? field.defaultValue;
}

function isBlank(value: unknown) {
  return value === undefined || value === null || (typeof value === "string" && value.trim().length === 0);
}

function formatDate(value?: string | null) {
  if (!value) return "-";
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return "-";
  return date.toLocaleString();
}

function appLink(app: string, workflowId?: string | null, runId?: string | null) {
  const base = APP_LINKS[app] || "/apps";
  if (!workflowId) return base;
  const params = new URLSearchParams({ workflow_id: workflowId });
  if (runId) params.set("run_id", runId);
  return `${base}?${params.toString()}`;
}

function StepRail({ active }: { active: "define" | "configure" | "run" }) {
  const steps = [
    { id: "define", label: "Define", text: "Create product" },
    { id: "configure", label: "Configure", text: "Review stages" },
    { id: "run", label: "Run", text: "Track results" },
  ] as const;
  return (
    <div className="grid gap-2 rounded-lg border border-slate-800 bg-slate-900/45 p-3 sm:grid-cols-3">
      {steps.map((step, index) => (
        <div
          key={step.id}
          className={`rounded-md border px-3 py-2 ${
            active === step.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-950/60"
          }`}
        >
          <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">Step {index + 1}</div>
          <div className={active === step.id ? "text-sm font-semibold text-cyan-100" : "text-sm font-semibold text-white"}>{step.label}</div>
          <div className="mt-1 text-xs text-slate-400">{step.text}</div>
        </div>
      ))}
    </div>
  );
}

export default function ProductDetailPage() {
  const params = useParams<{ productId: string }>();
  const router = useRouter();
  const productId = params.productId;
  const [product, setProduct] = useState<Product | null>(null);
  const [loading, setLoading] = useState(true);
  const [saving, setSaving] = useState(false);
  const [running, setRunning] = useState(false);
  const [message, setMessage] = useState<string | null>(null);
  const [selectedStageId, setSelectedStageId] = useState<string | null>(null);
  const [productRun, setProductRun] = useState<ProductRun | null>(null);
  const [stageRuns, setStageRuns] = useState<StageRun[]>([]);
  const [runHistory, setRunHistory] = useState<ProductRunWithStages[]>([]);
  const [stageSchemas, setStageSchemas] = useState<Record<string, StageSchema>>(FALLBACK_STAGE_SCHEMAS);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const schemas = await apiGet<{ status: string; stage_schemas: Record<string, StageSchema> }>("/products/stage-schemas");
        if (mounted && schemas.stage_schemas) setStageSchemas(schemas.stage_schemas);
      } catch {
        // Keep local fallback schemas during rollout or local backend mismatch.
      }
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const out = await apiGet<{ status: string; product: Product }>(`/products/${productId}`);
        if (!mounted) return;
        setProduct(out.product);
        setSelectedStageId(out.product.stage_config?.stages?.[0]?.id || null);
        try {
          const history = await apiGet<{ status: string; product_runs: ProductRunWithStages[] }>(`/products/${productId}/runs`);
          if (!mounted) return;
          setRunHistory(history.product_runs || []);
          const latest = history.product_runs?.[0];
          if (latest) {
            setProductRun(latest);
            setStageRuns(latest.stage_runs || []);
          }
        } catch {
          // Run history is non-blocking; product configuration should still load.
        }
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to load product");
      } finally {
        if (mounted) setLoading(false);
      }
    })();
    return () => { mounted = false; };
  }, [productId]);

  const stages = useMemo(() => product?.stage_config?.stages || [], [product]);
  const selectedStage = stages.find((stage) => stage.id === selectedStageId) || stages[0] || null;
  const stageRunById = useMemo(() => {
    const out: Record<string, StageRun> = {};
    for (const stageRun of stageRuns) out[stageRun.stage_id] = stageRun;
    return out;
  }, [stageRuns]);
  const missingRequirements = useMemo(() => {
    if (!product) return [];
    const missing: Array<{ stageId: string; stageLabel: string; fieldLabel: string }> = [];
    for (const stage of stages) {
      if (!stageEnabled(stage)) continue;
      const schema = stageSchemas[stage.app];
      for (const field of schema?.fields || []) {
        if (field.required && isBlank(fieldValue(stage, field))) {
          missing.push({ stageId: stage.id, stageLabel: stage.label, fieldLabel: field.label });
        }
      }
      if (stage.app === "Digital_Arch2RTL") {
        const specText = String(stage.settings?.spec_text || "").trim();
        if (!specText && !String(product.description || "").trim()) {
          missing.push({ stageId: stage.id, stageLabel: stage.label, fieldLabel: "Spec text or product description" });
        }
      }
    }
    return missing;
  }, [product, stages, stageSchemas]);
  const activeRun = Boolean(productRun && ["queued", "running"].includes(productRun.status));
  const failedStageRun = stageRuns.find((stageRun) => stageRun.status === "failed") || null;
  const failedStage = failedStageRun ? stages.find((stage) => stage.id === failedStageRun.stage_id) || null : null;
  const runCounts = useMemo(() => ({
    completed: stageRuns.filter((stageRun) => stageRun.status === "completed").length,
    failed: stageRuns.filter((stageRun) => stageRun.status === "failed").length,
    running: stageRuns.filter((stageRun) => ["queued", "running"].includes(stageRun.status)).length,
  }), [stageRuns]);

  useEffect(() => {
    if (!productRun || !product || !["queued", "running"].includes(productRun.status)) return;
    let mounted = true;
    const poll = async () => {
      try {
        const out = await apiGet<{ status: string; product_run: ProductRun; stage_runs: StageRun[] }>(
          `/products/${product.id}/runs/${productRun.id}`,
        );
        if (!mounted) return;
        setProductRun(out.product_run);
        setStageRuns(out.stage_runs || []);
        setRunHistory((current) => current.map((run) => (
          run.id === out.product_run.id ? { ...out.product_run, stage_runs: out.stage_runs || [] } : run
        )));
        if (!["queued", "running"].includes(out.product_run.status)) setRunning(false);
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to refresh product run");
      }
    };
    const timer = window.setInterval(() => { void poll(); }, 2500);
    void poll();
    return () => {
      mounted = false;
      window.clearInterval(timer);
    };
  }, [productRun, product]);

  function updateStage(stageId: string, patch: Partial<Stage>) {
    setProduct((current) => {
      if (!current) return current;
      const nextStages = (current.stage_config?.stages || []).map((stage) => (
        stage.id === stageId ? { ...stage, ...patch } : stage
      ));
      return {
        ...current,
        stage_config: {
          ...(current.stage_config || {}),
          stages: nextStages,
        },
      };
    });
  }

  function updateStageSetting(stageId: string, key: string, value: unknown) {
    setProduct((current) => {
      if (!current) return current;
      const nextStages = (current.stage_config?.stages || []).map((stage) => {
        if (stage.id !== stageId) return stage;
        return {
          ...stage,
          settings: {
            ...(stage.settings || {}),
            [key]: value,
          },
        };
      });
      return {
        ...current,
        stage_config: {
          ...(current.stage_config || {}),
          stages: nextStages,
        },
      };
    });
  }

  async function saveDraft() {
    if (!product) return;
    setSaving(true);
    setMessage(null);
    try {
      const out = await apiPatch<{ status: string; product: Product }>(`/products/${product.id}`, {
        stage_config: product.stage_config || {},
        status: product.status,
      });
      setProduct(out.product);
      setMessage("Product draft saved.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to save product");
    } finally {
      setSaving(false);
    }
  }

  async function runProduct(startStage?: string, resumeProductRunId?: string) {
    if (!product) return;
    if (missingRequirements.length) {
      setMessage("Complete required configuration before running the product.");
      setSelectedStageId(missingRequirements[0].stageId);
      return;
    }
    setRunning(true);
    setMessage(null);
    try {
      await saveDraft();
      const out = await apiPost<{ status: string; product_run: ProductRun }>(`/products/${product.id}/run`, {
        max_stages: 8,
        start_stage: startStage,
        resume_product_run_id: resumeProductRunId,
      });
      setProductRun(out.product_run);
      setStageRuns([]);
      setRunHistory((current) => [{ ...out.product_run, stage_runs: [] }, ...current.filter((run) => run.id !== out.product_run.id)]);
      setMessage(startStage ? `Product run restarted from ${startStage}.` : "Product run started. Supported stages run in order with workflow handoffs.");
    } catch (error) {
      setRunning(false);
      setMessage(error instanceof Error ? error.message : "Failed to start product run");
    }
  }

  async function cancelRun() {
    if (!product || !productRun) return;
    setMessage(null);
    try {
      const out = await apiPost<{ status: string; product_run: ProductRun }>(`/products/${product.id}/runs/${productRun.id}/cancel`, {});
      setProductRun(out.product_run);
      setRunHistory((current) => current.map((run) => (run.id === out.product_run.id ? { ...run, ...out.product_run } : run)));
      setRunning(false);
      setMessage("Product run cancellation requested. The orchestrator will stop before the next stage.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to cancel product run");
    }
  }

  async function skipFailedOptionalStage() {
    if (!product || !failedStage || failedStage.required) return;
    const nextStages = stages.map((stage) => (
      stage.id === failedStage.id ? { ...stage, enabled: false } : stage
    ));
    const nextStageConfig = { ...(product.stage_config || {}), stages: nextStages };
    setProduct({ ...product, stage_config: nextStageConfig });
    setSelectedStageId(failedStage.id);
    setSaving(true);
    setMessage(null);
    try {
      const out = await apiPatch<{ status: string; product: Product }>(`/products/${product.id}`, {
        stage_config: nextStageConfig,
        status: product.status,
      });
      setProduct(out.product);
      setMessage(`${failedStage.label} will be skipped on the next run.`);
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to skip optional stage");
    } finally {
      setSaving(false);
    }
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-slate-950 text-slate-100">
        <TopNav current="products" showPlanBadge />
        <div className="mx-auto max-w-7xl px-4 py-8 text-sm text-slate-300">Loading product...</div>
      </main>
    );
  }

  if (!product) {
    return (
      <main className="min-h-screen bg-slate-950 text-slate-100">
        <TopNav current="products" showPlanBadge />
        <div className="mx-auto max-w-7xl px-4 py-8">
          <div className="rounded-lg border border-rose-500/30 bg-rose-950/30 p-4 text-sm text-rose-100">{message || "Product not found."}</div>
          <button onClick={() => router.push("/products")} className="mt-4 rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-200 hover:bg-slate-800">Back to Products</button>
        </div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-slate-950 text-slate-100">
      <TopNav current="products" showPlanBadge />
      <div className="mx-auto max-w-7xl px-4 py-6 sm:px-6">
        <div className="mb-5 flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
          <div>
            <button onClick={() => router.push("/products")} className="mb-3 text-sm font-semibold text-cyan-300 hover:text-cyan-200">Back to Products</button>
            <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Step 2: Configure Product</div>
            <h1 className="mt-2 text-3xl font-bold tracking-normal text-white">{product.name}</h1>
            <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">{product.description || "Review stages, configure required inputs, then run product development."}</p>
            <div className="mt-3 flex flex-wrap gap-2 text-xs">
              <span className="rounded-md bg-slate-800 px-2 py-1 text-slate-300">{typeLabel(product.product_type)}</span>
              <span className="rounded-md bg-slate-800 px-2 py-1 text-slate-300">{product.starting_point.replace(/_/g, " ")}</span>
              <span className="rounded-md border border-slate-700 px-2 py-1 text-slate-300">{product.status}</span>
            </div>
          </div>
          <div className="flex gap-2">
            <button onClick={saveDraft} disabled={saving} className="rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300 disabled:opacity-60">
              {saving ? "Saving..." : "Save Draft"}
            </button>
            <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800">
              Open Apps
            </button>
          </div>
        </div>

        <div className="mb-5">
          <StepRail active="configure" />
        </div>

        {message ? <div className="mb-5 rounded-lg border border-cyan-500/30 bg-cyan-950/30 px-4 py-3 text-sm text-cyan-100">{message}</div> : null}

        <div className="grid gap-5 lg:grid-cols-[0.95fr_1.05fr]">
          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
            <div className="flex items-center justify-between gap-3">
              <div>
                <h2 className="text-xl font-semibold text-white">Development Stages</h2>
                <p className="mt-1 text-sm text-slate-400">Required stages stay enabled. Recommended and optional stages can be switched off.</p>
              </div>
              <span className="rounded-md bg-slate-950 px-2 py-1 text-xs text-slate-300">{stages.length} stages</span>
            </div>
            <div className="mt-5 space-y-3">
              {stages.length === 0 ? (
                <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">No stages configured yet.</div>
              ) : stages.map((stage, index) => (
                <button
                  key={stage.id}
                  onClick={() => setSelectedStageId(stage.id)}
                  className={`w-full rounded-lg border p-4 text-left transition ${
                    selectedStage?.id === stage.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-950/60 hover:border-slate-600"
                  }`}
                >
                  <div className="flex items-start justify-between gap-3">
                    <div>
                      <div className="text-xs font-semibold text-slate-500">Stage {index + 1}</div>
                      <div className="mt-1 font-semibold text-white">{stage.label}</div>
                      <div className="mt-1 text-xs text-slate-400">{stage.app}</div>
                    </div>
                    <div className="text-right">
                      <div className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300">{stageKind(stage)}</div>
                      <div className={`mt-2 text-xs font-semibold ${
                        stageRunById[stage.id]?.status === "completed"
                          ? "text-emerald-300"
                          : stageRunById[stage.id]?.status === "failed"
                          ? "text-rose-300"
                          : stageRunById[stage.id]?.status === "running"
                          ? "text-cyan-300"
                          : stageEnabled(stage)
                          ? "text-emerald-300"
                          : "text-slate-500"
                      }`}>
                        {stageRunById[stage.id]?.status || (stageEnabled(stage) ? "Enabled" : "Skipped")}
                      </div>
                    </div>
                  </div>
                </button>
              ))}
            </div>
          </section>

          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
            {selectedStage ? (
              <>
                <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
                  <div>
                    <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">{stageKind(selectedStage)}</div>
                    <h2 className="mt-2 text-xl font-semibold text-white">{selectedStage.label}</h2>
                    <p className="mt-1 text-sm text-slate-400">{selectedStage.app}</p>
                  </div>
                  <div className="flex gap-2">
                    {!selectedStage.required ? (
                      <button
                        onClick={() => updateStage(selectedStage.id, { enabled: !stageEnabled(selectedStage) })}
                        className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                      >
                        {stageEnabled(selectedStage) ? "Skip" : "Enable"}
                      </button>
                    ) : null}
                    <button
                      onClick={() => router.push(APP_LINKS[selectedStage.app] || "/apps")}
                      className="rounded-lg bg-slate-100 px-3 py-2 text-sm font-semibold text-slate-950 hover:bg-white"
                    >
                      Open App
                    </button>
                  </div>
                </div>

                <div className="mt-5 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                  <h3 className="font-semibold text-white">Configuration</h3>
                  <p className="mt-1 text-sm text-slate-400">Stage settings are saved with the product. Workflow IDs from earlier stages are auto-bound during Run.</p>
                  {stageSchemas[selectedStage.app]?.note ? (
                    <div className="mt-3 rounded-md border border-cyan-500/20 bg-cyan-950/20 px-3 py-2 text-xs leading-5 text-cyan-100">
                      {stageSchemas[selectedStage.app]?.note}
                    </div>
                  ) : null}
                  <div className="mt-4 grid gap-3">
                    {(stageSchemas[selectedStage.app] || FALLBACK_STAGE_SCHEMA).fields.map((field) => {
                      const value = fieldValue(selectedStage, field);
                      if (field.type === "boolean") {
                        return (
                          <label key={field.key} className="flex items-center justify-between gap-3 rounded-lg border border-slate-800 bg-slate-900/60 px-3 py-2">
                            <span className="text-sm text-slate-200">{field.label}</span>
                            <input
                              type="checkbox"
                              checked={Boolean(value)}
                              onChange={(event) => updateStageSetting(selectedStage.id, field.key, event.target.checked)}
                              className="h-4 w-4 accent-cyan-400"
                            />
                          </label>
                        );
                      }
                      return (
                        <label key={field.key} className="grid gap-2">
                          <span className="text-sm font-medium text-slate-200">
                            {field.label}{field.required ? <span className="text-rose-300"> *</span> : null}
                          </span>
                          <input
                            type={field.type}
                            value={String(value)}
                            onChange={(event) => updateStageSetting(selectedStage.id, field.key, field.type === "number" ? Number(event.target.value) : event.target.value)}
                            className={`rounded-lg border bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400 ${
                              field.required && isBlank(value) ? "border-rose-500/70" : "border-slate-700"
                            }`}
                          />
                          {field.helper ? <span className="text-xs text-slate-500">{field.helper}</span> : null}
                        </label>
                      );
                    })}
                  </div>
                </div>

                <div className="mt-5 rounded-lg border border-cyan-500/25 bg-cyan-950/15 p-4 text-sm leading-6 text-cyan-100">
                  Product Run uses existing App workflows and passes generated workflow IDs between stages. Existing standalone Apps and reference journeys remain available.
                </div>
              </>
            ) : (
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">Select a stage to configure it.</div>
            )}
          </section>
        </div>

        <section className="mt-5 rounded-lg border border-slate-800 bg-slate-900/45 p-5">
          <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Step 3: Run</div>
              <h2 className="mt-2 text-xl font-semibold text-white">Product run dashboard</h2>
              <p className="mt-1 max-w-3xl text-sm leading-6 text-slate-400">
                This launches supported enabled stages in order, passes workflow IDs between stages, stops on failures, and shows product-level results.
              </p>
            </div>
            <button
              onClick={() => runProduct()}
              disabled={running || activeRun || missingRequirements.length > 0}
              className="rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
            >
              {running || activeRun ? "Running..." : "Run Product"}
            </button>
          </div>
          {missingRequirements.length ? (
            <div className="mt-4 rounded-lg border border-rose-500/30 bg-rose-950/25 p-4">
              <div className="text-sm font-semibold text-rose-100">Required inputs missing</div>
              <div className="mt-2 grid gap-2">
                {missingRequirements.map((item) => (
                  <button
                    key={`${item.stageId}-${item.fieldLabel}`}
                    onClick={() => setSelectedStageId(item.stageId)}
                    className="rounded-md border border-rose-500/20 bg-slate-950/50 px-3 py-2 text-left text-xs text-rose-100 hover:border-rose-400/60"
                  >
                    {item.stageLabel}: {item.fieldLabel}
                  </button>
                ))}
              </div>
            </div>
          ) : null}
          {productRun ? (
            <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="flex flex-col gap-2 sm:flex-row sm:items-center sm:justify-between">
                <div>
                  <div className="text-sm font-semibold text-white">Run {productRun.id}</div>
                  <div className="mt-1 text-xs text-slate-500">
                    Updated {formatDate(productRun.updated_at)} | Completed {formatDate(productRun.completed_at)}
                  </div>
                  <div className="mt-2 flex flex-wrap gap-2 text-xs">
                    <span className="rounded-md bg-emerald-500/10 px-2 py-1 text-emerald-200">{runCounts.completed} completed</span>
                    <span className="rounded-md bg-cyan-500/10 px-2 py-1 text-cyan-200">{runCounts.running} active</span>
                    <span className="rounded-md bg-rose-500/10 px-2 py-1 text-rose-200">{runCounts.failed} failed</span>
                  </div>
                  <div className="mt-1 text-xs text-slate-400">Status: {productRun.status}{productRun.current_stage ? ` · Current: ${productRun.current_stage}` : ""}</div>
                </div>
                <div className="flex flex-wrap items-center gap-2">
                  {activeRun ? (
                    <button onClick={cancelRun} className="rounded-md border border-rose-500/50 px-3 py-2 text-xs font-semibold text-rose-100 hover:bg-rose-950/50">
                      Cancel
                    </button>
                  ) : null}
                  {productRun.status === "failed" && failedStageRun ? (
                    <button
                      onClick={() => runProduct(failedStageRun.stage_id, productRun.id)}
                      className="rounded-md border border-cyan-500/50 px-3 py-2 text-xs font-semibold text-cyan-100 hover:bg-cyan-950/50"
                    >
                      Rerun From Failed Stage
                    </button>
                  ) : null}
                  {productRun.status === "failed" && failedStage && !failedStage.required ? (
                    <button
                      onClick={skipFailedOptionalStage}
                      className="rounded-md border border-slate-600 px-3 py-2 text-xs font-semibold text-slate-200 hover:bg-slate-800"
                    >
                      Skip Optional Stage
                    </button>
                  ) : null}
                  {productRun.error ? <div className="text-xs text-rose-300">{productRun.error}</div> : null}
                </div>
              </div>
              {stageRuns.length ? (
                <div className="mt-4 grid gap-2">
                  {stageRuns.map((stageRun) => (
                    <div key={stageRun.id} className="flex flex-col gap-2 rounded-lg border border-slate-800 bg-slate-900/60 px-3 py-2 sm:flex-row sm:items-center sm:justify-between">
                      <div>
                        <div className="text-sm font-semibold text-white">{stageRun.stage_label}</div>
                        <div className="text-xs text-slate-500">{stageRun.app}</div>
                      </div>
                      <div className="flex items-center gap-2">
                        {stageRun.workflow_id ? (
                          <>
                            <button
                              onClick={() => router.push(appLink(stageRun.app, stageRun.workflow_id, stageRun.run_id))}
                              className="rounded-md border border-cyan-700/70 px-2 py-1 text-xs text-cyan-100 hover:bg-cyan-950/40"
                            >
                              Open App
                            </button>
                            <a
                              href={`/api/workflow/${stageRun.workflow_id}/download_zip?full=1`}
                              className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-800"
                            >
                              Download ZIP
                            </a>
                          </>
                        ) : null}
                        <span className={`rounded-md px-2 py-1 text-xs ${
                          stageRun.status === "completed"
                            ? "bg-emerald-500/10 text-emerald-200"
                            : stageRun.status === "failed"
                            ? "bg-rose-500/10 text-rose-200"
                            : "bg-cyan-500/10 text-cyan-200"
                        }`}>
                          {stageRun.status}
                        </span>
                      </div>
                      <div className="text-xs text-slate-500 sm:basis-full">
                        Started {formatDate(stageRun.started_at)} | Completed {formatDate(stageRun.completed_at)}
                      </div>
                      {stageRun.error ? <div className="text-xs text-rose-300 sm:basis-full">{stageRun.error}</div> : null}
                    </div>
                  ))}
                </div>
              ) : null}
            </div>
          ) : null}
          {runHistory.length ? (
            <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Run history</div>
              <div className="mt-3 grid gap-2">
                {runHistory.slice(0, 8).map((run) => (
                  <button
                    key={run.id}
                    onClick={() => {
                      setProductRun(run);
                      setStageRuns(run.stage_runs || []);
                    }}
                    className={`flex flex-col gap-1 rounded-lg border px-3 py-2 text-left transition sm:flex-row sm:items-center sm:justify-between ${
                      productRun?.id === run.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-900/60 hover:border-slate-600"
                    }`}
                  >
                    <span className="text-xs text-slate-300">{run.id}</span>
                    <span className={`rounded-md px-2 py-1 text-xs ${
                      run.status === "completed"
                        ? "bg-emerald-500/10 text-emerald-200"
                        : run.status === "failed"
                        ? "bg-rose-500/10 text-rose-200"
                        : "bg-cyan-500/10 text-cyan-200"
                    }`}>
                      {run.status}
                    </span>
                  </button>
                ))}
              </div>
            </div>
          ) : null}
          <div className="mt-4 grid gap-3 sm:grid-cols-3">
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Automatic handoff</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">RTL, verify, firmware, software, validation, and product app workflow IDs will be bound automatically.</p>
            </div>
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Gated execution</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">Required stages must pass before dependent stages run. Optional stages can be skipped.</p>
            </div>
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Integrated results</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">The product dashboard will link each stage dashboard and summarize coverage, artifacts, and blockers.</p>
            </div>
          </div>
        </section>
      </div>
    </main>
  );
}
