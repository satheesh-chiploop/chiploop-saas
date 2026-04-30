"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import SettingsNav from "../SettingsNav";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type Entitlements = Record<string, boolean | number | string | null | undefined>;

type PlanSummary = {
  current_plan?: {
    id?: string;
    name?: string;
    display_name?: string;
    price_monthly_usd?: number | null;
  };
  price?: number | string | null;
  base_price?: number | string | null;
  discounted_price?: number | null;
  price_monthly?: number | null;
  credits?: number | null;
  monthly_credits?: number | null;
  credits_used?: number;
  credits_remaining?: number | null;
  entitlements?: Entitlements;
  billing_status?: string;
  trial?: {
    status?: string | null;
    days_remaining?: number | null;
    trial_end_at?: string | null;
    auto_renew?: boolean;
    converts_to?: string | null;
  };
  trial_days_remaining?: number | null;
  discount_months_remaining?: number;
  upgrade_hint?: {
    show?: boolean;
    type?: string | null;
    target_plan?: string | null;
    message?: string;
  };
  suggested_upgrade?: {
    show?: boolean;
    type?: string | null;
    target_plan?: string | null;
    message?: string;
  };
};

type PlanResponse = {
  status: string;
  plan: PlanSummary;
};

const featureLabels: Record<string, string> = {
  sdk_cli_enabled: "SDK/CLI",
  agent_planner_enabled: "Agent Planner",
  agent_factory_dry_run_enabled: "Agent Factory dry-run",
  private_agent_save_enabled: "Private agent save",
  dag_optimization_enabled: "DAG optimization",
  marketplace_submit_enabled: "Marketplace submission",
  agent_factory_write_enabled: "Agent Factory write mode",
  higher_workflow_limits: "Higher workflow limits",
  custom_limits: "Custom limits",
};

function formatCredits(value?: number | null): string {
  if (value === null || value === undefined) return "Custom";
  return value.toLocaleString();
}

function errorMessage(error: unknown): string {
  if (error instanceof ApiClientError && error.status === 401) {
    return "Your session expired. Please sign in again.";
  }
  if (error instanceof Error) return error.message;
  return "Failed to load plan.";
}

export default function SettingsPlanPage() {
  const router = useRouter();
  const [plan, setPlan] = useState<PlanSummary | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  async function loadPlan() {
    setLoading(true);
    setError(null);
    try {
      const data = await apiGet<PlanResponse>("/settings/plan");
      setPlan(data.plan || {});
    } catch (err) {
      setError(errorMessage(err));
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadPlan();
  }, []);

  const entitlements = useMemo(() => plan?.entitlements || {}, [plan?.entitlements]);
  const enabledFeatures = useMemo(
    () =>
      Object.entries(featureLabels).map(([key, label]) => ({
        key,
        label,
        enabled: Boolean(entitlements[key]),
      })),
    [entitlements]
  );

  const planName = plan?.current_plan?.display_name || plan?.current_plan?.name || "Trial";
  const monthlyCredits = plan?.credits ?? plan?.monthly_credits;
  const usedCredits = plan?.credits_used ?? 0;
  const remainingCredits = plan?.credits_remaining;
  const progress = monthlyCredits && monthlyCredits > 0 ? Math.min(100, Math.round((usedCredits / monthlyCredits) * 100)) : 0;
  const trial = plan?.trial;
  const activePrice = plan?.price_monthly ?? plan?.discounted_price ?? plan?.base_price ?? plan?.price;
  const basePrice = plan?.base_price ?? plan?.price;
  const discountMonthsRemaining = plan?.discount_months_remaining ?? 0;

  return (
    <SettingsNav>
      <div className="space-y-6">
        <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
          <div className="flex flex-col gap-4 md:flex-row md:items-center md:justify-between">
            <div>
              <h2 className="text-xl font-bold">Plan</h2>
              <p className="mt-1 text-sm text-slate-400">
                Your current plan, monthly credits, and enabled Phase 8 features.
              </p>
            </div>
            <div className="flex gap-2">
              <button
                onClick={loadPlan}
                disabled={loading}
                className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 transition hover:bg-slate-900 disabled:cursor-not-allowed disabled:text-slate-500"
              >
                {loading ? "Refreshing..." : "Refresh"}
              </button>
              <button
                onClick={() => router.push("/pricing")}
                className="rounded-lg bg-cyan-700 px-4 py-2 text-sm font-semibold text-white transition hover:bg-cyan-600"
              >
                View plans
              </button>
            </div>
          </div>
        </section>

        {error ? (
          <div className="rounded-lg border border-red-900/70 bg-red-950/30 p-4 text-sm text-red-200">
            {error}
          </div>
        ) : null}

        {loading ? (
          <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-6 text-sm text-slate-400">
            Loading plan...
          </div>
        ) : plan ? (
          <>
            {trial?.status ? (
              <section className="rounded-lg border border-cyan-700/50 bg-cyan-950/20 p-5">
                <div className="text-sm font-semibold text-cyan-100">Trial status</div>
                <div className="mt-2 text-sm text-cyan-100/85">
                  {trial.status === "active"
                    ? `${trial.days_remaining ?? "-"} days remaining. Starter is $19.99/month after 30 days. Cancel anytime before trial ends.`
                    : `Trial ${trial.status}.`}
                </div>
              </section>
            ) : null}

            <section className="grid gap-4 md:grid-cols-5">
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Current plan</div>
                <div className="mt-2 text-2xl font-extrabold text-cyan-200">{planName}</div>
                <div className="mt-1 text-xs uppercase tracking-wide text-slate-500">
                  {plan.billing_status || "placeholder"}
                </div>
              </div>
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Monthly price</div>
                <div className="mt-2 text-2xl font-extrabold text-slate-100">
                  {typeof activePrice === "number" ? `$${activePrice.toFixed(2)}` : activePrice || "Custom"}
                </div>
                {discountMonthsRemaining > 0 ? (
                  <div className="mt-1 text-xs text-cyan-200">
                    Discount active, then {typeof basePrice === "number" ? `$${basePrice.toFixed(2)}` : basePrice}
                  </div>
                ) : null}
              </div>
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Monthly credits</div>
                <div className="mt-2 text-2xl font-extrabold text-slate-100">{formatCredits(monthlyCredits)}</div>
              </div>
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Used credits</div>
                <div className="mt-2 text-2xl font-extrabold text-slate-100">{formatCredits(usedCredits)}</div>
              </div>
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="text-sm text-slate-400">Remaining credits</div>
                <div className="mt-2 text-2xl font-extrabold text-emerald-200">{formatCredits(remainingCredits)}</div>
              </div>
            </section>

            {discountMonthsRemaining > 0 ? (
              <section className="rounded-lg border border-cyan-700/50 bg-cyan-950/20 p-5">
                <div className="text-sm font-semibold text-cyan-100">Intro discount</div>
                <div className="mt-2 text-sm text-cyan-100/85">
                  25% off remains for {discountMonthsRemaining} billing cycle{discountMonthsRemaining === 1 ? "" : "s"}.
                </div>
              </section>
            ) : null}

            {monthlyCredits ? (
              <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
                <div className="mb-2 flex items-center justify-between text-sm text-slate-300">
                  <span>Credit usage</span>
                  <span>{progress}% used</span>
                </div>
                <div className="h-3 overflow-hidden rounded-full bg-slate-800">
                  <div className="h-full bg-cyan-600" style={{ width: `${progress}%` }} />
                </div>
              </section>
            ) : null}

            <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-5">
              <h3 className="text-lg font-bold">Enabled features</h3>
              <div className="mt-4 grid gap-3 md:grid-cols-2">
                {enabledFeatures.map((feature) => (
                  <div key={feature.key} className="flex items-center justify-between rounded-lg border border-slate-800 bg-black/30 px-4 py-3">
                    <span className="text-sm text-slate-200">{feature.label}</span>
                    <span className={`rounded-full px-2 py-1 text-xs ${feature.enabled ? "border border-emerald-700 bg-emerald-950/40 text-emerald-200" : "border border-slate-700 bg-slate-900 text-slate-400"}`}>
                      {feature.enabled ? "Enabled" : "Disabled"}
                    </span>
                  </div>
                ))}
              </div>
            </section>

            <section className="rounded-lg border border-amber-700/40 bg-amber-950/20 p-5">
              <h3 className="font-bold text-amber-100">Upgrade placeholder</h3>
              <p className="mt-1 text-sm text-amber-100/80">
Trial checkout will require Stripe card setup. Starter is $19.99/month after 30 days. Starter, Pro, and Pro Max receive 25% off for the first 3 billing cycles after checkout is connected. Enterprise remains contact-sales only.
              </p>
            </section>
          </>
        ) : null}
      </div>
    </SettingsNav>
  );
}





