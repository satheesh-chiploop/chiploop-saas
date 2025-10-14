"use client";

import { useEffect, useMemo, useState, Suspense } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

// ✅ Supabase init
const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

type PlanKey = "freemium" | "single" | "double" | "all";

const BASE_PRICES: Record<PlanKey, number> = {
  freemium: 0,
  single: 19.99,
  double: 29.99,
  all: 39.99,
};

const prettyPlanName: Record<PlanKey, string> = {
  freemium: "Freemium",
  single: "Single Loop",
  double: "Double Loop",
  all: "All Loops",
};

function PricingContent() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);
  const [isStudent, setIsStudent] = useState(false);
  const [currentPlan, setCurrentPlan] = useState<PlanKey>("freemium");
  const [loadingPortal, setLoadingPortal] = useState(false);
  const [subscribing, setSubscribing] = useState<PlanKey | null>(null);

  // 🧑‍💻 Session & current plan (best-effort from "workflows" table)
  useEffect(() => {
    const init = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const email = session?.user?.email ?? null;
      setUserEmail(email);

      if (!email) return;

      try {
        // Try to read current plan from the "workflows" table
        // Expecting optional columns like "current_plan" or "subscription_status"
        const { data, error } = await supabase
          .from("workflows")
          .select("current_plan, subscription_status")
          .eq("user_id", email)
          .limit(1)
          .maybeSingle();

        if (!error && data) {
          const planFromDB =
            (data.current_plan as PlanKey | null) ||
            (data.subscription_status as PlanKey | null);

          if (
            planFromDB &&
            ["freemium", "single", "double", "all"].includes(planFromDB)
          ) {
            setCurrentPlan(planFromDB as PlanKey);
          } else {
            setCurrentPlan("freemium");
          }
        }
      } catch {
        // ignore and keep default
      }
    };
    init();
  }, []);

  // 🎚️ Student discount
  const priceFor = (plan: PlanKey) => {
    const base = BASE_PRICES[plan];
    if (base === 0) return "Free";
    if (!isStudent) return `$${base.toFixed(2)}/mo`;
    const discounted = Math.max(0, base * 0.75);
    return `$${discounted.toFixed(2)}/mo`;
  };

  // 🧭 Top-right button logic
  const topCtaText = userEmail ? "🚀 Go to Workflow" : "🔑 Login";
  const onTopCta = () => (userEmail ? router.push("/workflow") : router.push("/login"));

  // 🧾 Subscribe handler
  const subscribe = async (plan: PlanKey) => {
    if (plan === "freemium") {
      // For freemium, just send them to login or workflow
      onTopCta();
      return;
    }
    try {
      setSubscribing(plan);
      // Must have a user session to start checkout
      const { data: { session } } = await supabase.auth.getSession();
      const token = session?.access_token;
      if (!token) {
        router.push("/login");
        return;
      }

      const res = await fetch("/api/create-checkout-session", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: `Bearer ${token}`,
        },
        body: JSON.stringify({
          plan,         // "single" | "double" | "all"
          student: isStudent,
        }),
      });

      const data = await res.json();
      if (data?.url) window.location.href = data.url;
      else alert("❌ Failed to start checkout.");
    } catch (err) {
      console.error(err);
      alert("❌ Error starting checkout.");
    } finally {
      setSubscribing(null);
    }
  };

  // ⚙️ Manage subscription (Stripe customer portal)
  const openPortal = async () => {
    try {
      setLoadingPortal(true);
      const { data: { session } } = await supabase.auth.getSession();
      const token = session?.access_token;
      if (!token) {
        router.push("/login");
        return;
      }
      const res = await fetch("/api/create-customer-portal-session", {
        method: "POST",
        headers: { Authorization: `Bearer ${token}` },
      });
      const data = await res.json();
      if (data?.url) window.location.href = data.url;
      else alert("❌ Failed to open customer portal.");
    } catch (e) {
      console.error(e);
      alert("❌ Error opening customer portal.");
    } finally {
      setLoadingPortal(false);
    }
  };

  // 🔲 Plan cards config
  const plans: Array<{
    key: PlanKey;
    features: string[];
    cta: string;
  }> = useMemo(
    () => [
      {
        key: "freemium",
        features: ["1 Agent", "1 Workflow"],
        cta: userEmail ? "Start Free" : "Login to Start",
      },
      {
        key: "single",
        features: ["Any 1 Loop (Digital / Analog / Embedded)"],
        cta: "Subscribe",
      },
      {
        key: "double",
        features: ["Any 2 Loops"],
        cta: "Subscribe",
      },
      {
        key: "all",
        features: ["All 3 Loops (Full Platform Access)"],
        cta: "Subscribe",
      },
    ],
    [userEmail]
  );

  return (
    <main className="min-h-screen flex flex-col items-center justify-between bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white">
      {/* 🧭 Header */}
      <nav className="w-full flex justify-between items-center px-8 py-5 bg-black/70 backdrop-blur border-b border-slate-800 fixed top-0 left-0 z-50">
        <div
          onClick={() => router.push("/")}
          className="text-2xl font-extrabold text-cyan-400 cursor-pointer"
        >
          CHIPLOOP ⚡
        </div>
        <div className="flex space-x-8 text-slate-300 font-medium">
          <button onClick={() => router.push("/")} className="hover:text-cyan-400 transition">
            Home
          </button>
          <button onClick={() => router.push("/pricing")} className="hover:text-cyan-400 transition">
            Pricing
          </button>
        </div>
        <button
          onClick={onTopCta}
          className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-5 py-2 rounded-lg shadow-lg"
        >
          {topCtaText}
        </button>
      </nav>

      {/* 💳 Hero */}
      <section className="w-full max-w-5xl mx-auto text-center px-6 mt-32 mb-10">
        <h1 className="text-5xl md:text-6xl font-extrabold text-white mb-4">
          Choose Your Plan
        </h1>
        <p className="text-slate-300">
          Upgrade, downgrade, or manage your ChipLoop subscription anytime.
        </p>
        <div className="mt-3 text-sm text-slate-400">
          Current Plan:&nbsp;
          <span className="text-cyan-400 font-semibold">
            {prettyPlanName[currentPlan]}
          </span>
        </div>
      </section>

      {/* 🎚️ Regular ↔ Student toggle */}
      <section className="mb-10">
        <div className="flex items-center gap-4 bg-slate-800/70 px-4 py-2 rounded-full border border-slate-700">
          <span className={!isStudent ? "text-cyan-400 font-semibold" : "text-slate-300"}>
            Regular
          </span>
          <label className="inline-flex items-center cursor-pointer select-none">
            <input
              type="checkbox"
              checked={isStudent}
              onChange={(e) => setIsStudent(e.target.checked)}
              className="sr-only peer"
            />
            <div className="w-14 h-8 bg-slate-700 rounded-full peer-checked:bg-cyan-500 transition relative">
              <span className="absolute top-1 left-1 w-6 h-6 bg-white rounded-full transition peer-checked:translate-x-6" />
            </div>
          </label>
          <span className={isStudent ? "text-cyan-400 font-semibold" : "text-slate-300"}>
            Student&nbsp;🎓&nbsp;25% Off
          </span>
        </div>
      </section>

      {/* 💠 Plan Cards */}
      <section className="w-full max-w-6xl grid grid-cols-1 md:grid-cols-4 gap-6 px-6 mb-16">
        {plans.map(({ key, features, cta }) => {
          const isCurrent = currentPlan === key;
          return (
            <div
              key={key}
              className={`p-6 rounded-xl shadow-lg border ${
                isCurrent ? "border-cyan-400" : "border-slate-700"
              } bg-slate-800/70 hover:bg-slate-700 transition`}
            >
              <div className="mb-4">
                <h3 className="text-2xl font-bold text-white">{prettyPlanName[key]}</h3>
                <p className="text-cyan-400 text-xl mt-2">{priceFor(key)}</p>
              </div>

              <ul className="text-slate-300 text-sm space-y-2 mb-6">
                {features.map((f) => (
                  <li key={f}>✅ {f}</li>
                ))}
                {key === "freemium" && <li>✅ Free forever</li>}
              </ul>

              {isCurrent ? (
                <div className="text-center">
                  <div className="text-cyan-400 font-semibold mb-3">Current Plan</div>
                  <button
                    onClick={openPortal}
                    disabled={loadingPortal}
                    className="w-full bg-emerald-600 hover:bg-emerald-500 disabled:opacity-60 text-white font-bold py-2 rounded-lg"
                  >
                    {loadingPortal ? "Opening..." : "Manage Subscription"}
                  </button>
                </div>
              ) : (
                <button
                  onClick={() => subscribe(key)}
                  disabled={subscribing === key}
                  className="w-full bg-cyan-500 hover:bg-cyan-400 disabled:opacity-60 text-black font-bold py-2 rounded-lg"
                >
                  {subscribing === key ? "Processing..." : cta}
                </button>
              )}
            </div>
          );
        })}
      </section>

      {/* Footer */}
      <footer className="w-full border-t border-slate-800 py-8 text-center text-slate-400 text-sm bg-black/70">
        <p>© 2025 ChipLoop</p>
        <div className="mt-2 space-x-4 text-slate-500">
          <button onClick={() => router.push("/privacy")}>Privacy</button>
          <button onClick={() => router.push("/terms")}>Terms</button>
        </div>
      </footer>
    </main>
  );
}

export default function PricingPage() {
  return (
    <Suspense fallback={<div className="text-center p-10 text-white">Loading...</div>}>
      <PricingContent />
    </Suspense>
  );
}
