"use client";

import { Suspense, useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type PlanKey = "trial" | "starter" | "pro" | "pro_max" | "enterprise";

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
  "App workflows",
  "SDK/CLI",
  "API keys",
  "Agent Planner",
  "Agent Factory dry-run",
  "Private agents",
  "DAG optimization",
  "Marketplace submission",
  "Support",
];

const plans: Plan[] = [
  {
    key: "trial",
    name: "Trial",
    price: "Free for 30 days",
    credits: "100 trial credits",
    cta: "Start free trial",
    note: "Credit card required. No charge during trial. Auto-converts to Starter unless canceled.",
    features: {
      "App workflows": "Trial access",
      "SDK/CLI": "Limited test access",
      "API keys": "1 test key",
      "Agent Planner": "Included",
      "Agent Factory dry-run": "Limited",
      "Private agents": "1 private agent",
      "DAG optimization": "Not included",
      "Marketplace submission": "Not included",
      Support: "Standard",
    },
  },
  {
    key: "starter",
    name: "Starter",
    price: "$19.99/month",
    discountPrice: "$14.99/month for first 3 months",
    credits: "2,000 credits/month",
    cta: "Coming soon",
    note: "For individual developers starting production workflows.",
    features: {
      "App workflows": "Included",
      "SDK/CLI": "Included",
      "API keys": "1 key",
      "Agent Planner": "Included",
      "Agent Factory dry-run": "Included",
      "Private agents": "5 private agents",
      "DAG optimization": "Limited",
      "Marketplace submission": "Not included",
      Support: "Standard",
    },
  },
  {
    key: "pro",
    name: "Pro",
    price: "$39.99/month",
    discountPrice: "$29.99/month for first 3 months",
    credits: "5,000 credits/month",
    cta: "Coming soon",
    note: "For regular Studio users building custom workflows and agents.",
    popular: true,
    features: {
      "App workflows": "Included",
      "SDK/CLI": "Included",
      "API keys": "3 keys",
      "Agent Planner": "Included",
      "Agent Factory dry-run": "Included",
      "Private agents": "25 private agents",
      "DAG optimization": "Included",
      "Marketplace submission": "Included",
      Support: "Priority",
    },
  },
  {
    key: "pro_max",
    name: "Pro Max",
    price: "$59.99/month",
    discountPrice: "$44.99/month for first 3 months",
    credits: "12,000 credits/month",
    cta: "Coming soon",
    note: "For heavier automation and larger Studio usage.",
    features: {
      "App workflows": "Higher limits",
      "SDK/CLI": "Included",
      "API keys": "10 keys",
      "Agent Planner": "Included",
      "Agent Factory dry-run": "Included",
      "Private agents": "100 private agents",
      "DAG optimization": "Included",
      "Marketplace submission": "Included",
      Support: "Priority",
    },
  },
  {
    key: "enterprise",
    name: "Enterprise",
    price: "Custom",
    credits: "Custom credits",
    cta: "Contact sales",
    note: "For organizations needing custom limits, support, and deployment review.",
    features: {
      "App workflows": "Custom limits",
      "SDK/CLI": "Included",
      "API keys": "Custom",
      "Agent Planner": "Included",
      "Agent Factory dry-run": "Included",
      "Private agents": "Custom",
      "DAG optimization": "Included",
      "Marketplace submission": "Included",
      Support: "Dedicated",
    },
  },
];

function normalizePlanId(value?: string): PlanKey | null {
  if (!value) return null;
  const key = value.toLowerCase().replace(/\s+/g, "_") as PlanKey;
  return plans.some((plan) => plan.key === key) ? key : null;
}

function PricingContent() {
  const router = useRouter();
  const [currentPlan, setCurrentPlan] = useState<PlanKey | null>(null);

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
    return plans.find((plan) => plan.key === currentPlan)?.name || null;
  }, [currentPlan]);

  function handlePlanAction(plan: Plan) {
    if (plan.key === "enterprise") {
      window.location.href = "mailto:sales@chiploop.com?subject=ChipLoop%20Enterprise";
      return;
    }
    if (plan.key === "trial") {
      router.push("/login?mode=signup&trial=1");
      return;
    }
    router.push("/settings/plan");
  }

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <nav className="sticky top-0 z-50 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-7xl items-center justify-between px-6 py-4">
          <button onClick={() => router.push("/")} className="text-2xl font-extrabold text-cyan-400">
            CHIPLOOP
          </button>
          <div className="flex items-center gap-5 text-sm font-medium text-slate-300">
            <button onClick={() => router.push("/apps")} className="hover:text-cyan-300">Apps</button>
            <button onClick={() => router.push("/workflow")} className="hover:text-cyan-300">Studio</button>
            <button onClick={() => router.push("/settings/plan")} className="hover:text-cyan-300">Settings</button>
          </div>
        </div>
      </nav>

      <section className="mx-auto max-w-7xl px-6 py-12">
        <div className="max-w-3xl">
          <h1 className="text-4xl font-extrabold tracking-tight md:text-5xl">Pricing</h1>
          <p className="mt-4 text-lg text-slate-300">
            Start with a free 30-day trial. Paid plans get 25% off for the first 3 months. Cancel before trial ends to avoid conversion.
          </p>
          {currentPlanName ? (
            <div className="mt-4 inline-flex rounded-lg border border-cyan-700/60 bg-cyan-950/30 px-3 py-2 text-sm text-cyan-100">
              Current plan: {currentPlanName}
            </div>
          ) : null}
        </div>

        <section className="mt-10 grid gap-4 lg:grid-cols-5">
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
                  className={`mt-5 w-full rounded-lg px-4 py-2 text-sm font-bold transition ${plan.key === "enterprise" ? "border border-slate-600 text-slate-100 hover:bg-slate-900" : "bg-cyan-600 text-white hover:bg-cyan-500"}`}
                >
                  {isCurrent ? "Current plan" : plan.cta}
                </button>
              </article>
            );
          })}
        </section>

        <section className="mt-10 overflow-hidden rounded-lg border border-slate-800 bg-slate-950/70">
          <div className="border-b border-slate-800 px-5 py-4">
            <h2 className="text-xl font-bold">Feature comparison</h2>
            <p className="mt-1 text-sm text-slate-400">Trial checkout will require a credit card through Stripe. Paid-plan checkout is enabled only after server-side Stripe price IDs and coupons are configured.</p>
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
