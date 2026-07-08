"use client";

import { useMemo } from "react";
import { useParams, useRouter, useSearchParams } from "next/navigation";
import TopNav from "@/components/TopNav";
import WorkflowEvidenceDashboard from "@/components/WorkflowEvidenceDashboard";

type DashboardStage = "arch2rtl" | "dqa" | "smoke" | "synthesis" | "tapeout" | "verification" | "embedded" | "software" | "validation" | "product";

const VALID_STAGES = new Set<DashboardStage>([
  "arch2rtl",
  "dqa",
  "smoke",
  "synthesis",
  "tapeout",
  "verification",
  "embedded",
  "software",
  "validation",
  "product",
]);

function parseStage(value: string | null): DashboardStage {
  return value && VALID_STAGES.has(value as DashboardStage) ? value as DashboardStage : "arch2rtl";
}

export default function WorkflowDashboardPage() {
  const params = useParams<{ workflowId: string }>();
  const searchParams = useSearchParams();
  const router = useRouter();
  const workflowId = params.workflowId;
  const stage = parseStage(searchParams.get("stage"));
  const status = searchParams.get("status") || "completed";
  const app = searchParams.get("app") || "";

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
              Workflow {workflowId}{app ? ` | ${app}` : ""} | {stage}
            </p>
          </div>
          <a
            href={downloadHref}
            className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
          >
            Download ZIP
          </a>
        </div>

        <WorkflowEvidenceDashboard workflowId={workflowId} status={status} stage={stage} />
      </div>
    </main>
  );
}
