"use client";

import { useEffect, useMemo, useState } from "react";
import { useParams, useRouter, useSearchParams } from "next/navigation";
import TopNav from "@/components/TopNav";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";
import AskThisRunPanel from "@/components/AskThisRunPanel";
import { createClientComponentClient } from "@/lib/platformClient";

type DashboardStage = "physical_ai" | "arch2rtl" | "dqa" | "rtl_review" | "constraint_review" | "timing_debug" | "smoke" | "synthesis" | "tapeout" | "fpga" | "fpga_target_explorer" | "verification" | "embedded" | "software" | "validation" | "product";

const VALID_STAGES = new Set<DashboardStage>([
  "physical_ai",
  "arch2rtl",
  "dqa",
  "rtl_review",
  "constraint_review",
  "timing_debug",
  "smoke",
  "synthesis",
  "tapeout",
  "fpga",
  "fpga_target_explorer",
  "verification",
  "embedded",
  "software",
  "validation",
  "product",
]);

const STAGE_LABELS: Record<DashboardStage, string> = {
  physical_ai: "Physical AI / Application Intelligence",
  arch2rtl: "RTL Generation",
  dqa: "Design Quality",
  rtl_review: "RTL Review",
  constraint_review: "Constraint Review",
  timing_debug: "Timing Debug",
  smoke: "Smoke Verification",
  synthesis: "Synthesis",
  tapeout: "ASIC Implementation",
  fpga: "FPGA Implementation",
  fpga_target_explorer: "FPGA Target Explorer",
  verification: "RTL Verification",
  embedded: "Firmware",
  software: "Software",
  validation: "Validation",
  product: "Product",
};

function parseStage(value: string | null): DashboardStage {
  return value && VALID_STAGES.has(value as DashboardStage) ? value as DashboardStage : "arch2rtl";
}

function stageFromWorkflowDefinition(definitions: unknown, requestedStage: DashboardStage): DashboardStage {
  if (!definitions || typeof definitions !== "object" || Array.isArray(definitions)) return requestedStage;
  const definition = definitions as Record<string, unknown>;
  const hemStage = String(definition.hem_stage || "").trim().toLowerCase();
  // Supabase is authoritative for workflow identity. Derive presentation from
  // the durable HEM stage so stale dashboard metadata cannot mislabel old runs.
  const hemDashboardStages: Record<string, DashboardStage> = {
    arch2rtl: "arch2rtl",
    verify: "verification",
    fpga_exploration: "fpga_target_explorer",
    fpga_bitstream: "fpga",
    asic_tapeout: "tapeout",
    firmware_product: "embedded",
    system_dqa: "dqa",
    system_sim: "verification",
    system_firmware: "embedded",
    system_software: "software",
    system_software_validation_l2: "validation",
    system_product_app_builder: "product",
    system_synthesis: "synthesis",
    system_pd: "tapeout",
  };
  if (hemDashboardStages[hemStage]) return hemDashboardStages[hemStage];
  const dashboardStage = String(definition.hem_dashboard_stage || "").trim();
  return VALID_STAGES.has(dashboardStage as DashboardStage)
    ? dashboardStage as DashboardStage
    : requestedStage;
}

export default function WorkflowDashboardPage() {
  const params = useParams<{ workflowId: string }>();
  const searchParams = useSearchParams();
  const router = useRouter();
  const workflowId = params.workflowId;
  const requestedStage = parseStage(searchParams.get("stage"));
  const requestedStatus = searchParams.get("status") || "running";
  const app = searchParams.get("app") || "";
  const supabase = useMemo(() => createClientComponentClient(), []);
  const [workflowState, setWorkflowState] = useState<{ status: string; phase: string; logs: string; hasArtifacts: boolean | null; stage: DashboardStage }>({
    status: requestedStatus,
    phase: "",
    logs: "",
    hasArtifacts: null,
    stage: requestedStage,
  });

  useEffect(() => {
    let active = true;
    let interval: number | null = null;
    const load = async () => {
      const { data, error } = await supabase
        .from("workflows")
        .select("status,phase,logs,artifacts,definitions")
        .eq("id", workflowId)
        .single();
      if (!active || error || !data) return;
      const row = data as { status?: string | null; phase?: string | null; logs?: string | null; artifacts?: unknown; definitions?: unknown };
      setWorkflowState({
        status: row.status || requestedStatus,
        phase: row.phase || "",
        logs: row.logs || "",
        hasArtifacts: artifactIndexHasEntries(row.artifacts),
        stage: stageFromWorkflowDefinition(row.definitions, requestedStage),
      });
    };
    void load();
    interval = window.setInterval(() => void load(), 2500);
    return () => {
      active = false;
      if (interval) window.clearInterval(interval);
    };
  }, [requestedStage, requestedStatus, supabase, workflowId]);

  const stage = workflowState.stage;

  const downloadHref = useMemo(
    () => `/api/workflow/${encodeURIComponent(workflowId)}/download_zip?full=1`,
    [workflowId],
  );

  return (
    <main className="min-h-screen bg-slate-950 text-slate-100">
      <TopNav current="apps" showPlanBadge />
      <div className="mx-auto max-w-[1680px] px-4 py-6 sm:px-6">
        <div className="mb-5 flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
          <div>
            <button onClick={() => router.back()} className="mb-3 text-sm font-semibold text-cyan-300 hover:text-cyan-200">
              Back
            </button>
            <div className="text-xs font-semibold uppercase text-cyan-300">Workflow Dashboard</div>
            <h1 className="mt-2 text-3xl font-bold tracking-normal text-white">Dashboard Results</h1>
            <p className="mt-2 max-w-3xl break-words text-sm leading-6 text-slate-300">
              Workflow {workflowId}{app ? ` | ${app}` : ""} | {STAGE_LABELS[stage]}
            </p>
          </div>
          <div className="flex flex-wrap items-center gap-2">
            <span className="rounded-full border border-slate-700 bg-slate-900 px-3 py-2 text-xs font-semibold uppercase text-slate-300">
              {workflowState.status}{workflowState.phase ? ` · ${workflowState.phase}` : ""}
            </span>
            {workflowState.hasArtifacts === true ? (
              <a href={downloadHref} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800">
                Download ZIP
              </a>
            ) : workflowState.hasArtifacts === false ? (
              <span className="cursor-not-allowed rounded-lg border border-slate-800 px-4 py-2 text-sm font-semibold text-slate-500" title="No artifacts were indexed for this workflow. Review its status and logs below.">
                No artifacts
              </span>
            ) : (
              <span className="rounded-lg border border-slate-800 px-4 py-2 text-sm font-semibold text-slate-500">Checking artifacts...</span>
            )}
          </div>
        </div>

        <WorkflowEvidenceDashboard workflowId={workflowId} status={workflowState.status} stage={stage} logs={workflowState.logs} />
        <div className="mt-5">
          <AskThisRunPanel workflowId={workflowId} />
        </div>
      </div>
    </main>
  );
}

function artifactIndexHasEntries(value: unknown): boolean {
  if (typeof value === "string") return value.trim().length > 0;
  if (Array.isArray(value)) return value.some(artifactIndexHasEntries);
  if (value && typeof value === "object") return Object.values(value as Record<string, unknown>).some(artifactIndexHasEntries);
  return false;
}
