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
  loopAccess: string;
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
  "Included Loop Access",
  "Monthly Credits",
  "Guided Apps",
  "Product Journeys",
  "Ask this Project",
  "Design Intent Analyzer",
  "Studio Access",
  "Workflow Composer",
  "Create App from Workflow",
  "Private Apps / Workflows",
  "Custom Agents",
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
    credits: "500 credits/month",
    loopAccess: "1 Loop Core",
    cta: "Start Starter",
    note: "For individuals starting with one chip design loop, guided apps, and basic Studio configuration.",
    features: {
      "Included Loop Access": "1 Loop Core",
      "Monthly Credits": "500, no rollover",
      "Guided Apps": "Included",
      "Product Journeys": "Subscribed loop only",
      "Ask this Project": "Included",
      "Design Intent Analyzer": "Basic",
      "Studio Access": "Basic configuration",
      "Workflow Composer": "Use templates",
      "Create App from Workflow": "Limited",
      "Private Apps / Workflows": "1-2 private apps",
      "Custom Agents": "Not included",
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
    price: "$49.99/month",
    discountPrice: "$39.99/month for first 3 months",
    credits: "2,500 credits/month",
    loopAccess: "3 Loop Core or 1 Loop Advanced",
    cta: "Start Pro",
    note: "For active users who need more loops, custom workflows, app creation, SDK, and CLI.",
    popular: true,
    features: {
      "Included Loop Access": "3 Loop Core or 1 Loop Advanced",
      "Monthly Credits": "2,500, no rollover",
      "Guided Apps": "Included",
      "Product Journeys": "Subscribed loops",
      "Ask this Project": "Included",
      "Design Intent Analyzer": "Advanced",
      "Studio Access": "Create and edit",
      "Workflow Composer": "Included",
      "Create App from Workflow": "Included",
      "Private Apps / Workflows": "Higher limits",
      "Custom Agents": "Limited",
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
    price: "$99.99/month",
    discountPrice: "$79.99/month for first 3 months",
    credits: "12,000 credits/month",
    loopAccess: "All Loops Advanced",
    cta: "Start Pro Max",
    note: "For users and teams running advanced flows across every chip design loop.",
    features: {
      "Included Loop Access": "All Loops Advanced",
      "Monthly Credits": "12,000, no rollover",
      "Guided Apps": "Included",
      "Product Journeys": "All subscribed journeys",
      "Ask this Project": "Included",
      "Design Intent Analyzer": "Advanced + team context",
      "Studio Access": "Advanced",
      "Workflow Composer": "Included",
      "Create App from Workflow": "Included",
      "Private Apps / Workflows": "High limits",
      "Custom Agents": "Included",
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
    loopAccess: "Custom loop access",
    cta: "Contact Sales",
    note: "For pilots, beta programs, custom limits, governance, and private deployment review.",
    features: {
      "Included Loop Access": "Custom",
      "Monthly Credits": "Custom",
      "Guided Apps": "Custom limits",
      "Product Journeys": "Custom",
      "Ask this Project": "Included",
      "Design Intent Analyzer": "Custom/private context",
      "Studio Access": "Full",
      "Workflow Composer": "Included",
      "Create App from Workflow": "Included",
      "Private Apps / Workflows": "Custom",
      "Custom Agents": "Custom",
      "Developer Automation: SDK + CLI": "Included",
      "API Keys": "Custom",
      "Marketplace Access": "Optional / governed",
      "Submit to Marketplace": "Optional / governed",
      Support: "Enterprise SLA / pilot support",
    },
  },
];

const loopPackages = [
  ["Digital Design", "Spec capture, Arch2RTL, RTL review, smoke compile/sim, DQA, basic verification setup", "Spec2RTL conformance, deeper DQA, assertions, coverage planning, verification closure analysis"],
  ["Digital Implementation", "Synthesis setup, synthesis run, constraints, timing/power/area reports", "Auto synthesis closure, LEC, scan/DFT, ATPG, MBIST, RTL-to-GDS, STA, signoff"],
  ["Mixed Signal", "System RTL, analog/digital interface intent, behavioral models, smoke tests, System Sim, System Synthesis", "System DQA, integration debug, mixed-signal evidence, System PD/signoff path, validation handoff"],
  ["Firmware/Software", "Register-map extraction, HAL/driver scaffolds, boot setup, diagnostics, firmware build/run", "Software SDK/API generation, package validation, hardware/software co-simulation, integration debug, demo package"],
  ["Validation", "Validation plan, bench/instrument setup, connectivity and wiring intent, preflight, run review", "Execution orchestration, analytics, pattern detection, coverage proposals, plan evolution"],
];

const addOns = [
  ["Add one Loop Core", "+$4.99/month", "Add another engineering domain at Core depth."],
  ["Upgrade Loop to Advanced", "+$9.99/month", "Unlock Advanced capability for a loop you already have."],
  ["Add one Loop Advanced", "+$14.99/month", "Add a new engineering domain directly at Advanced depth."],
  ["500 extra credits", "$9.99", "One-time credit pack for additional usage."],
  ["1,500 extra credits", "$24.99", "One-time credit pack for heavier short-term usage."],
  ["5,000 extra credits", "$69.99", "One-time credit pack for larger workflow runs."],
];

const setupSteps = [
  ["1", "Choose included loop", "After signup, select the Core loop included with your plan."],
  ["2", "Add capability", "Upgrade that loop to Advanced or add another Core/Advanced loop."],
  ["3", "Add usage", "Buy extra credits only when you need more runs."],
];

function normalizePlanId(value?: string): CurrentPlanKey | null {
  if (!value) return null;
  const normalized = value.toLowerCase().replace(/\s+/g, "_");
  if (normalized === "trial" || normalized === "free") return "trial";
  const key = normalized as CurrentPlanKey;
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
    if (currentPlan === "trial") return "3-day Trial";
    return plans.find((plan) => plan.key === currentPlan)?.name || null;
  }, [currentPlan]);

  async function startCheckout(planId: PlanKey, options: { trial?: boolean } = {}) {
    setCheckoutPlan(options.trial ? "trial" : planId);
    setCheckoutError(null);
    try {
      const response = await apiPost<{ status: string; url?: string }>("/settings/billing/checkout", {
        plan_id: planId,
        trial: Boolean(options.trial),
      });
      if (!response.url) throw new Error("Checkout URL was not returned.");
      window.location.href = response.url;
    } catch (error) {
      if (error instanceof ApiClientError && error.status === 401) {
        const trialParam = options.trial ? "&trial=1" : "";
        router.push(`/login?mode=signup${trialParam}&plan=${planId}&next=${encodeURIComponent("/pricing")}`);
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
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="pricing" showMarketplace showSettings={false} />

      <section className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-6 py-12">
        <div className="mx-auto max-w-[1680px]">
        <div className="max-w-3xl">
          <h1 className="text-5xl font-extrabold leading-[1.05] text-white md:text-6xl">Pricing</h1>
          <p className="mt-4 text-lg text-slate-300">
            Choose a platform plan, then use the chip design loops your work needs. Core covers normal
            generate, configure, run, and review flows. Advanced adds deeper analysis, closure, debug,
            signoff, validation, and automation.
          </p>
          <p className="mt-3 text-sm text-slate-400">
            Monthly credits control usage and do not roll over. Advanced loop upgrades unlock capability;
            extra credits are purchased separately when users need more runs.
          </p>
          <div className="mt-5 flex flex-wrap gap-3">
            <button
              onClick={() => document.getElementById("setup-flow")?.scrollIntoView({ behavior: "smooth", block: "start" })}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
            >
              How loop add-ons work
            </button>
            <button
              onClick={() => router.push("/settings/plan")}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200"
            >
              Plan Settings
            </button>
          </div>
          {currentPlanName ? (
            <div className="mt-4 inline-flex rounded-lg border border-slate-700 bg-slate-950/60 px-3 py-2 text-sm text-slate-200">
              Current plan: {currentPlanName}
            </div>
          ) : null}
          {checkoutError ? (
            <div className="mt-4 rounded-lg border border-red-900/70 bg-red-950/30 px-3 py-2 text-sm text-red-200">
              {checkoutError}
            </div>
          ) : null}
        </div>

        <section className="mt-8 rounded-lg border border-slate-800 bg-slate-950/70 p-5">
          <div className="flex flex-col gap-3 md:flex-row md:items-center md:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase text-cyan-300">Starter intro</div>
              <p className="mt-2 text-sm leading-6 text-slate-300">
                Start at $14.99/month for the first 3 months, then $19.99/month. Includes 1 Loop Core and 500 monthly credits.
              </p>
            </div>
            <button
              onClick={() => startCheckout("starter")}
              disabled={checkoutPlan !== null}
              className="rounded-lg bg-cyan-600 px-5 py-3 text-sm font-bold text-white transition hover:bg-cyan-500 disabled:cursor-not-allowed disabled:bg-slate-700"
            >
              {checkoutPlan === "starter" ? "Opening checkout..." : "Start Starter"}
            </button>
          </div>
        </section>

        <section className="mt-10 grid gap-4 lg:grid-cols-4">
          {plans.map((plan) => {
            const isCurrent = currentPlan === plan.key;
            return (
              <article key={plan.key} className={`relative rounded-lg border p-5 ${plan.popular ? "border-cyan-500 bg-slate-950/80" : isCurrent ? "border-cyan-500 bg-slate-950/70" : "border-slate-800 bg-slate-950/70"}`}>
                {plan.popular ? (
                  <div className="absolute right-3 top-3 rounded-full bg-cyan-500 px-3 py-1 text-xs font-bold text-black">Most Popular</div>
                ) : null}
                <div className="min-h-48 pt-2">
                  <h2 className="text-xl font-bold text-white">{plan.name}</h2>
                  <div className="mt-3 text-2xl font-extrabold text-cyan-200">{plan.discountPrice || plan.price}</div>
                  {plan.discountPrice ? <div className="mt-1 text-sm text-slate-400">Then {plan.price}</div> : null}
                  <div className="mt-2 text-sm font-semibold text-slate-300">{plan.credits}</div>
                  <div className="mt-1 text-sm font-semibold text-slate-200">{plan.loopAccess}</div>
                  <p className="mt-4 text-sm leading-6 text-slate-400">{plan.note}</p>
                  {plan.key !== "enterprise" ? (
                    <p className="mt-3 text-xs leading-5 text-slate-500">
                      After checkout, configure loops and add-ons from Plan Settings.
                    </p>
                  ) : null}
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

        <section id="setup-flow" className="mt-10 rounded-lg border border-slate-800 bg-slate-950/70 p-5 scroll-mt-24">
          <div className="max-w-3xl">
            <div className="text-xs font-semibold uppercase text-cyan-300">After Signup</div>
            <h2 className="mt-2 text-xl font-bold">Set up your loop access</h2>
            <p className="mt-2 text-sm leading-6 text-slate-300">
              Checkout starts the base subscription. Loop choices, Advanced upgrades, and credit packs are managed from Plan Settings after signup.
            </p>
          </div>
          <div className="mt-5 grid gap-4 md:grid-cols-3">
            {setupSteps.map(([step, title, body]) => (
              <article key={step} className="rounded-lg border border-slate-800 bg-slate-900/60 p-4">
                <div className="flex h-8 w-8 items-center justify-center rounded-full bg-cyan-400 text-sm font-extrabold text-slate-950">{step}</div>
                <h3 className="mt-3 font-extrabold text-white">{title}</h3>
                <p className="mt-2 text-sm leading-6 text-slate-300">{body}</p>
              </article>
            ))}
          </div>
          <div className="mt-5 flex flex-wrap gap-3">
            <button onClick={() => router.push("/settings/plan")} className="rounded-lg bg-cyan-500 px-5 py-3 text-sm font-bold text-slate-950 hover:bg-cyan-400">
              Open Plan Settings
            </button>
            <button onClick={() => document.getElementById("add-ons")?.scrollIntoView({ behavior: "smooth", block: "start" })} className="rounded-lg border border-slate-700 px-5 py-3 text-sm font-bold text-slate-200 hover:border-cyan-300 hover:text-cyan-200">
              View Add-ons
            </button>
          </div>
        </section>

        <section id="add-ons" className="mt-10 rounded-lg border border-slate-800 bg-slate-950/70 p-5 scroll-mt-24">
          <div className="max-w-3xl">
            <h2 className="text-xl font-bold">Five subscription loops</h2>
            <p className="mt-2 text-sm leading-6 text-slate-400">
              Product journeys unlock from the loops a user subscribes to. Advanced never replaces Core;
              it adds deeper analysis, checks, closure, debug, and signoff capability.
            </p>
          </div>
          <div className="mt-6 overflow-x-auto">
            <table className="w-full min-w-[920px] text-left text-sm">
              <thead className="bg-slate-900/80 text-slate-300">
                <tr>
                  <th className="px-4 py-3 font-semibold">Loop</th>
                  <th className="px-4 py-3 font-semibold">Core</th>
                  <th className="px-4 py-3 font-semibold">Advanced</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-800">
                {loopPackages.map(([loop, core, advanced]) => (
                  <tr key={loop}>
                    <td className="px-4 py-3 font-semibold text-slate-100">{loop}</td>
                    <td className="px-4 py-3 text-slate-300">{core}</td>
                    <td className="px-4 py-3 text-slate-300">{advanced}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </section>

        <section className="mt-10 rounded-lg border border-slate-800 bg-slate-950/70 p-5">
          <div className="max-w-3xl">
            <h2 className="text-xl font-bold">Loop and credit add-ons</h2>
            <p className="mt-2 text-sm leading-6 text-slate-400">
              Add loop access when users need more engineering domains. Add credits when users need more usage.
              Loop upgrades do not automatically add credits.
            </p>
          </div>
          <div className="mt-6 grid gap-4 md:grid-cols-2 xl:grid-cols-3">
            {addOns.map(([name, price, body]) => (
              <article key={name} className="rounded-lg border border-slate-800 bg-slate-900/70 p-4">
                <div className="text-base font-extrabold text-white">{name}</div>
                <div className="mt-2 text-xl font-extrabold text-white">{price}</div>
                <p className="mt-2 text-sm leading-6 text-slate-400">{body}</p>
              </article>
            ))}
          </div>
        </section>

        <section className="mt-10 overflow-hidden rounded-lg border border-slate-800 bg-slate-950/70">
          <div className="border-b border-slate-800 px-5 py-4">
            <h2 className="text-xl font-bold">Feature comparison</h2>
            <p className="mt-1 text-sm text-slate-400">
              Plans control platform capability. Loops control engineering domain access. Credits control how much users run.
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
        </div>
      </section>
      <footer className="border-t border-slate-800 px-6 py-8 text-center text-base text-slate-500">
        <div className="mb-4 flex flex-wrap justify-center gap-4 text-slate-400">
          <button onClick={() => router.push("/events")} className="hover:text-cyan-200">Events</button>
          <button onClick={() => router.push("/help")} className="hover:text-cyan-200">Playbook</button>
          <button onClick={() => router.push("/why-chiploop")} className="hover:text-cyan-200">Why ChipLoop</button>
          <button onClick={() => router.push("/webinar/register")} className="hover:text-cyan-200">Webinar</button>
          <button onClick={() => router.push("/contact")} className="hover:text-cyan-200">Contact Us</button>
        </div>
        <p className="mb-2 text-slate-300">Connect with us: chiploop.agx@gmail.com</p>
        <p>Copyright 2026 ChipLoop</p>
      </footer>
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




