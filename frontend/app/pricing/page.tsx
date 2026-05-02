"use client";

import { Suspense, useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";
import TopNav from "@/components/TopNav";

type PlanKey = "starter" | "pro" | "pro_max" | "enterprise";
type CurrentPlanKey = PlanKey | "trial";

type Plan = {
  key: PlanKey;
  name: string;
  price: string;
  discountPrice?: string;
  credits: string;
  cta: string;
  note: string;
  popular?: boolean;
  features: Record<string, string>;
};

type PlanResponse = {
  status: string;
  plan?: {
    current_plan?: { id?: string; name?: string; display_name?: string };
  };
};

const featureRows = [
  "Guided Apps",
  "Studio Access",
  "Agent Planner",
  "Draft Agent Generation",
  "Private Agents",
  "Optimize Workflow",
  "Developer Automation: SDK + CLI",
  "API Keys",
  "Marketplace Access",
  "Submit to Marketplace",
  "Support",
];

const plans: Plan[] = [
  {
    key: "starter",
    name: "Starter",
    price: "$19.99/month",
    discountPrice: "$14.99/month for first 3 months",
    credits: "2,000 credits/month",
    cta: "Start Starter",
    note: "For users running guided Apps and basic Studio workflows from the browser.",
    features: {
      "Guided Apps": "Included",
      "Studio Access": "Basic",
      "Agent Planner": "Included",
      "Draft Agent Generation": "Included",
      "Private Agents": "5 private agents",
      "Optimize Workflow": "Limited",
      "Developer Automation: SDK + CLI": "Not included",
      "API Keys": "Not included",
      "Marketplace Access": "Browse + install",
      "Submit to Marketplace": "Not included",
      Support: "Standard",
    },
  },
  {
    key: "pro",
    name: "Pro",
    price: "$39.99/month",
    discountPrice: "$29.99/month for first 3 months",
    credits: "5,000 credits/month",
    cta: "Start Pro",
    note: "For developers and teams automating ChipLoop with Studio, SDK, and CLI.",
    popular: true,
    features: {
      "Guided Apps": "Included",
      "Studio Access": "Full",
      "Agent Planner": "Included",
      "Draft Agent Generation": "Included",
      "Private Agents": "25 private agents",
      "Optimize Workflow": "Included",
      "Developer Automation: SDK + CLI": "Included",
      "API Keys": "3 keys",
      "Marketplace Access": "Browse + install",
      "Submit to Marketplace": "Included",
      Support: "Priority",
    },
  },
  {
    key: "pro_max",
    name: "Pro Max",
    price: "$59.99/month",
    discountPrice: "$44.99/month for first 3 months",
    credits: "12,000 credits/month",
    cta: "Start Pro Max",
    note: "For heavier automation, more private agents, and higher usage limits.",
    features: {
      "Guided Apps": "Higher limits",
      "Studio Access": "Full",
      "Agent Planner": "Included",
      "Draft Agent Generation": "Included",
      "Private Agents": "100 private agents",
      "Optimize Workflow": "Included",
      "Developer Automation: SDK + CLI": "Included",
      "API Keys": "10 keys",
      "Marketplace Access": "Browse + install",
      "Submit to Marketplace": "Included",
      Support: "Priority",
    },
  },
  {
    key: "enterprise",
    name: "Enterprise",
    price: "Custom",
    credits: "Custom credits",
    cta: "Contact Sales",
    note: "For pilots, beta programs, custom limits, governance, and private deployment review.",
    features: {
      "Guided Apps": "Custom limits",
      "Studio Access": "Full",
      "Agent Planner": "Included",
      "Draft Agent Generation": "Included",
      "Private Agents": "Custom",
      "Optimize Workflow": "Included",
      "Developer Automation: SDK + CLI": "Included",
      "API Keys": "Custom",
      "Marketplace Access": "Optional / governed",
      "Submit to Marketplace": "Optional / governed",
      Support: "Enterprise SLA / pilot support",
    },
  },
];

function normalizePlanId(value?: string): CurrentPlanKey | null {
  if (!value) return null;
  const key = value.toLowerCase().replace(/\s+/g, "_") as CurrentPlanKey;
  if (key === "trial" || key === "free") return "trial";
  return plans.some((plan) => plan.key === key) ? key : null;
}

function PricingContent() {
  const router = useRouter();
  const [currentPlan, setCurrentPlan] = useState<CurrentPlanKey | null>(null);
  const [checkoutPlan, setCheckoutPlan] = useState<PlanKey | "trial" | null>(null);
  const [checkoutError, setCheckoutError] = useState<string | null>(null);

  useEffect(() => {
    let cancelled = false;
    async function loadPlan() {
      try {
        const response = await apiGet<PlanResponse>("/settings/plan");
        const planId = normalizePlanId(response.plan?.current_plan?.id || response.plan?.current_plan?.name);
        if (!cancelled) setCurrentPlan(planId);
      } catch (error) {
        if (error instanceof ApiClientError && error.status === 401) return;
        console.warn("Plan lookup unavailable", error);
      }
    }
    loadPlan();
    return () => {
      cancelled = true;
    };
  }, []);

  const currentPlanName = useMemo(() => {
    if (!currentPlan) return null;
    if (currentPlan === "trial") return "7-day Trial";
    return plans.find((plan) => plan.key === currentPlan)?.name || null;
  }, [currentPlan]);

  async function startCheckout(planId: PlanKey) {
    setCheckoutPlan(planId);
    setCheckoutError(null);
    try {
      const response = await apiPost<{ status: string; url?: string }>("/settings/billing/checkout", { plan_id: planId });
      if (!response.url) throw new Error("Checkout URL was not returned.");
      window.location.href = response.url;
    } catch (error) {
      if (error instanceof ApiClientError && error.status === 401) {
        router.push(`/login?mode=signup&trial=1&plan=${planId}&next=${encodeURIComponent("/pricing")}`);
        return;
      }
      setCheckoutError(error instanceof Error ? error.message : "Checkout is unavailable right now.");
    } finally {
      setCheckoutPlan(null);
    }
  }

  function handlePlanAction(plan: Plan) {
    if (plan.key === "enterprise") {
      window.location.href = "mailto:sales@chiploop.com?subject=ChipLoop%20Enterprise%20Pilot";
      return;
    }
    startCheckout(plan.key);
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="pricing" showMarketplace showSettings={false} />

      <section className="mx-auto max-w-7xl px-6 py-12">
        <div className="max-w-3xl">
          <h1 className="text-4xl font-extrabold tracking-tight md:text-5xl">Pricing</h1>
          <p className="mt-4 text-lg text-slate-300">
            Choose the plan that matches how you use ChipLoop. Guided Apps and Studio start with Starter.
            Developer automation with SDK and CLI starts at Pro.
          </p>
          <p className="mt-3 text-sm text-cyan-100">
            Start with a 7-day trial, then auto-convert to Starter at $19.99/month unless canceled. Starter, Pro, and Pro Max receive 25% off for the first 3 months after checkout is connected.
          </p>
          {currentPlanName ? (
            <div className="mt-4 inline-flex rounded-lg border border-cyan-700/60 bg-cyan-950/30 px-3 py-2 text-sm text-cyan-100">
              Current plan: {currentPlanName}
            </div>
          ) : null}
          {checkoutError ? (
            <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 px-3 py-2 text-sm text-red-200">
              {checkoutError}
            </div>
          ) : null}
        </div>

        <section className="mt-8 rounded-lg border border-cyan-800/70 bg-cyan-950/25 p-5">
          <div className="flex flex-col gap-3 md:flex-row md:items-center md:justify-between">
            <div>
              <div className="text-sm font-bold uppercase tracking-wide text-cyan-300">7-day trial</div>
              <p className="mt-2 text-sm leading-6 text-cyan-50">
                Start with 100 credits. No charge during trial. Converts to Starter at $19.99/month after 7 days unless canceled.
              </p>
            </div>
            <button
              onClick={() => startCheckout("starter")}
              disabled={checkoutPlan !== null}
              className="rounded-lg bg-cyan-600 px-5 py-3 text-sm font-bold text-white transition hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
            >
              {checkoutPlan === "starter" ? "Opening checkout..." : "Start 7-day trial"}
            </button>
          </div>
        </section>

        <section className="mt-10 grid gap-4 lg:grid-cols-4">
          {plans.map((plan) => {
            const isCurrent = currentPlan === plan.key;
            return (
              <article key={plan.key} className={`relative rounded-lg border p-5 ${plan.popular ? "border-cyan-500 bg-cyan-950/20" : isCurrent ? "border-cyan-500 bg-slate-950/70" : "border-slate-800 bg-slate-950/70"}`}>
                {plan.popular ? (
                  <div className="absolute right-3 top-3 rounded-full bg-cyan-500 px-3 py-1 text-xs font-bold text-black">Most Popular</div>
                ) : null}
                <div className="min-h-48 pt-2">
                  <h2 className="text-xl font-bold text-white">{plan.name}</h2>
                  <div className="mt-3 text-2xl font-extrabold text-cyan-200">{plan.discountPrice || plan.price}</div>
                  {plan.discountPrice ? <div className="mt-1 text-sm text-slate-400">Then {plan.price}</div> : null}
                  <div className="mt-2 text-sm font-semibold text-slate-300">{plan.credits}</div>
                  <p className="mt-4 text-sm leading-6 text-slate-400">{plan.note}</p>
                </div>
                <button
                  onClick={() => handlePlanAction(plan)}
                  disabled={checkoutPlan !== null || isCurrent}
                  className={`mt-5 w-full rounded-lg px-4 py-2 text-sm font-bold transition disabled:cursor-not-allowed disabled:opacity-70 ${plan.key === "enterprise" ? "border border-slate-600 text-slate-100 hover:bg-slate-900" : "bg-cyan-600 text-white hover:bg-cyan-500"}`}
                >
                  {isCurrent ? "Current plan" : checkoutPlan === plan.key ? "Opening checkout..." : plan.cta}
                </button>
              </article>
            );
          })}
        </section>

        <section className="mt-10 overflow-hidden rounded-lg border border-slate-800 bg-slate-950/70">
          <div className="border-b border-slate-800 px-5 py-4">
            <h2 className="text-xl font-bold">Feature comparison</h2>
            <p className="mt-1 text-sm text-slate-400">
              SDK and CLI are premium developer automation features for Pro, Pro Max, and Enterprise. Enterprise can be used for pilots, beta programs, and custom deployment discussions.
            </p>
          </div>
          <div className="overflow-x-auto">
            <table className="w-full min-w-[980px] text-left text-sm">
              <thead className="bg-slate-900/80 text-slate-300">
                <tr>
                  <th className="px-4 py-3 font-semibold">Feature</th>
                  {plans.map((plan) => (
                    <th key={plan.key} className="px-4 py-3 font-semibold">{plan.name}</th>
                  ))}
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-800">
                {featureRows.map((feature) => (
                  <tr key={feature} className="text-slate-200">
                    <td className="px-4 py-3 font-semibold text-slate-100">{feature}</td>
                    {plans.map((plan) => (
                      <td key={`${plan.key}-${feature}`} className="px-4 py-3 text-slate-300">
                        {plan.features[feature]}
                      </td>
                    ))}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </section>
      </section>
    </main>
  );
}

export default function PricingPage() {
  return (
    <Suspense fallback={<div className="min-h-screen bg-black p-10 text-center text-white">Loading...</div>}>
      <PricingContent />
    </Suspense>
  );
}




