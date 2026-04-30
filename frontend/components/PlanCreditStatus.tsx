"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type PlanSummary = {
  current_plan?: {
    id?: string;
    name?: string;
    display_name?: string;
  };
  credits?: number | null;
  monthly_credits?: number | null;
  credits_used?: number | null;
  credits_remaining?: number | null;
  trial?: {
    status?: string | null;
    days_remaining?: number | null;
  };
  trial_days_remaining?: number | null;
};

type PlanResponse = {
  status: string;
  plan: PlanSummary;
};

type LoadState = {
  plan: PlanSummary | null;
  loading: boolean;
  error: string | null;
};

const LOW_CREDIT_DISMISS_KEY = "chiploop_low_credit_banner_dismissed_until";
const DISMISS_MS = 24 * 60 * 60 * 1000;

function formatCredits(value?: number | null): string {
  if (value === null || value === undefined) return "Custom";
  if (value >= 1000) return value.toLocaleString();
  return String(value);
}

function planName(plan: PlanSummary): string {
  return plan.current_plan?.display_name || plan.current_plan?.name || "Trial";
}

function trialDays(plan: PlanSummary): number | null {
  return plan.trial?.days_remaining ?? plan.trial_days_remaining ?? null;
}

function creditPercentRemaining(plan: PlanSummary): number | null {
  const monthly = plan.credits ?? plan.monthly_credits;
  const remaining = plan.credits_remaining;
  if (!monthly || monthly <= 0 || remaining === null || remaining === undefined) return null;
  return Math.max(0, Math.min(100, Math.round((remaining / monthly) * 100)));
}

function dismissalActive(): boolean {
  if (typeof window === "undefined") return true;
  const raw = window.localStorage.getItem(LOW_CREDIT_DISMISS_KEY);
  if (!raw) return false;
  const until = Number(raw);
  return !Number.isNaN(until) && Date.now() < until;
}

function dismissLowCredit() {
  if (typeof window === "undefined") return;
  window.localStorage.setItem(LOW_CREDIT_DISMISS_KEY, String(Date.now() + DISMISS_MS));
}

function usePlanSummary(): LoadState {
  const [state, setState] = useState<LoadState>({ plan: null, loading: true, error: null });

  useEffect(() => {
    let cancelled = false;
    async function loadPlan() {
      try {
        const response = await apiGet<PlanResponse>("/settings/plan");
        if (!cancelled) setState({ plan: response.plan || {}, loading: false, error: null });
      } catch (error) {
        if (cancelled) return;
        if (error instanceof ApiClientError && error.status === 401) {
          setState({ plan: null, loading: false, error: null });
          return;
        }
        setState({ plan: null, loading: false, error: "Plan unavailable" });
      }
    }
    loadPlan();
    return () => {
      cancelled = true;
    };
  }, []);

  return state;
}

export function PlanCreditBadge() {
  const router = useRouter();
  const { plan, loading, error } = usePlanSummary();
  const [open, setOpen] = useState(false);

  const summary = useMemo(() => {
    if (!plan) return null;
    const percent = creditPercentRemaining(plan);
    const days = trialDays(plan);
    return {
      name: planName(plan),
      remaining: plan.credits_remaining,
      monthly: plan.credits ?? plan.monthly_credits,
      used: plan.credits_used ?? 0,
      percent,
      days,
    };
  }, [plan]);

  if (loading || error || !summary) return null;

  const label = summary.days !== null && summary.name.toLowerCase().includes("trial")
    ? `${summary.name} · ${summary.days}d left · ${formatCredits(summary.remaining)} credits`
    : `${summary.name} · ${formatCredits(summary.remaining)} credits`;

  return (
    <div className="relative">
      <button
        type="button"
        onClick={() => setOpen((current) => !current)}
        className="rounded-xl border border-slate-700 bg-slate-950/50 px-3 py-2 text-xs font-semibold text-slate-200 transition hover:border-cyan-700 hover:bg-slate-900"
        title="Plan and credits"
      >
        {label}
      </button>
      {open ? (
        <div className="absolute right-0 z-50 mt-2 w-72 rounded-xl border border-slate-800 bg-slate-950 p-4 text-sm text-slate-200 shadow-2xl">
          <div className="flex items-start justify-between gap-3">
            <div>
              <div className="text-xs uppercase tracking-wide text-slate-500">Current plan</div>
              <div className="mt-1 font-bold text-cyan-200">{summary.name}</div>
            </div>
            {summary.days !== null ? (
              <div className="rounded-full border border-cyan-800 bg-cyan-950/40 px-2 py-1 text-xs text-cyan-100">
                {summary.days} days left
              </div>
            ) : null}
          </div>
          <div className="mt-4 grid grid-cols-2 gap-3 text-xs">
            <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="text-slate-500">Remaining</div>
              <div className="mt-1 text-lg font-bold text-emerald-200">{formatCredits(summary.remaining)}</div>
            </div>
            <div className="rounded-lg border border-slate-800 bg-black/30 p-3">
              <div className="text-slate-500">Monthly</div>
              <div className="mt-1 text-lg font-bold text-slate-100">{formatCredits(summary.monthly)}</div>
            </div>
          </div>
          {summary.percent !== null ? (
            <div className="mt-4">
              <div className="mb-1 flex justify-between text-xs text-slate-400">
                <span>Credits remaining</span>
                <span>{summary.percent}%</span>
              </div>
              <div className="h-2 overflow-hidden rounded-full bg-slate-800">
                <div className="h-full bg-cyan-600" style={{ width: `${summary.percent}%` }} />
              </div>
            </div>
          ) : null}
          <button
            type="button"
            onClick={() => router.push("/settings/plan")}
            className="mt-4 w-full rounded-lg border border-slate-700 px-3 py-2 text-xs font-semibold text-slate-200 transition hover:bg-slate-900"
          >
            View plan details
          </button>
        </div>
      ) : null}
    </div>
  );
}

export function LowCreditBanner() {
  const router = useRouter();
  const { plan, loading, error } = usePlanSummary();
  const [dismissed, setDismissed] = useState(false);

  const details = useMemo(() => {
    if (!plan) return null;
    const percent = creditPercentRemaining(plan);
    if (percent === null || percent >= 20) return null;
    return {
      name: planName(plan),
      percent,
      remaining: plan.credits_remaining,
    };
  }, [plan]);

  useEffect(() => {
    setDismissed(dismissalActive());
  }, []);

  if (loading || error || !details || dismissed) return null;

  return (
    <div className="border-b border-amber-800/50 bg-amber-950/20 px-4 py-2 text-sm text-amber-100">
      <div className="mx-auto flex max-w-6xl flex-col gap-2 md:flex-row md:items-center md:justify-between">
        <div>
          FYI: {details.name} has {details.percent}% credits remaining ({formatCredits(details.remaining)} left). Plan ahead for longer workflows.
        </div>
        <div className="flex shrink-0 gap-2">
          <button
            type="button"
            onClick={() => router.push("/settings/plan")}
            className="rounded-lg border border-amber-700/70 px-3 py-1 text-xs font-semibold text-amber-100 transition hover:bg-amber-900/30"
          >
            View plan
          </button>
          <button
            type="button"
            onClick={() => {
              dismissLowCredit();
              setDismissed(true);
            }}
            className="rounded-lg px-3 py-1 text-xs text-amber-100/80 transition hover:bg-amber-900/30"
          >
            Dismiss
          </button>
        </div>
      </div>
    </div>
  );
}
