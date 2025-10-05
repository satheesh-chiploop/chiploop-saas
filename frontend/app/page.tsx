"use client";

import { useEffect, useState, Suspense } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

interface Plan {
  name: string;
  price: number;
  description: string;
}

function LandingPageContent() {
  const router = useRouter();
  const [isSubscribed, setIsSubscribed] = useState(false);
  const [isLoggedIn, setIsLoggedIn] = useState(false);

  // ---------- Check if logged in ----------
  useEffect(() => {
    const checkLogin = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      setIsLoggedIn(!!session);
    };
    checkLogin();
  }, []);

  // ---------- Check subscription ----------
  useEffect(() => {
    const fetchSubscription = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const user = session?.user;
      if (!user?.email) return;

      const { data, error } = await supabase
        .from("subscriptions")
        .select("*")
        .eq("email", user.email)
        .single();

      if (!error && data) setIsSubscribed(true);
    };
    fetchSubscription();
  }, []);

  const plans: Plan[] = [
    { name: "Freemium", price: 0, description: "Try Digital Loop for free." },
    { name: "Basic", price: 19, description: "Full access with 1 workflow per day." },
  ];

  const handlePlanClick = async (plan: Plan) => {
    if (plan.price === 0) {
      // Freemium → go straight to workflow
      router.push("/workflow");
      return;
    }

    // Basic Plan → Stripe checkout
    try {
      const { data: { session } } = await supabase.auth.getSession();
      const token = session?.access_token;
      if (!token) {
        alert("⚠️ Please log in before subscribing.");
        return;
      }

      const res = await fetch("/api/create-checkout-session", {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: `Bearer ${token}`,
        },
        body: JSON.stringify({}),
      });

      const data = await res.json();
      if (data.url) {
        window.location.href = data.url;
      } else {
        alert("❌ Failed to start checkout");
      }
    } catch (err) {
      console.error(err);
      alert("⚠️ Unable to process subscription.");
    }
  };

  return (
    <main className="flex flex-col items-center justify-center min-h-screen bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white px-6">
      <h1 className="text-5xl font-extrabold mb-6 text-center">
        ⚙️ ChipLoop – Digital Loop MVP
      </h1>
      <p className="text-slate-300 max-w-2xl text-center mb-8">
        Run AI-powered chip workflows in one click. Choose your plan and get started instantly.
      </p>

      {/* ---------- CTA Buttons ---------- */}
      <div className="flex gap-4 mb-12">
        <button
          onClick={() => router.push("/workflow")}
          className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-3 rounded-xl shadow-lg transition"
        >
          🚀 Start Now
        </button>

        {!isLoggedIn && (
          <button
            onClick={() => router.push("/login")}
            className="bg-slate-700 hover:bg-slate-600 text-white font-bold px-6 py-3 rounded-xl shadow-lg transition"
          >
            🔑 Login
          </button>
        )}
      </div>

      {/* ---------- Pricing Cards ---------- */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-8">
        {plans.map((plan) => (
          <div
            key={plan.name}
            className="bg-slate-800 rounded-2xl p-8 text-center shadow-xl border border-slate-700"
          >
            <h2 className="text-3xl font-bold mb-2">{plan.name}</h2>
            <p className="text-slate-400 mb-4">{plan.description}</p>
            <p className="text-4xl font-extrabold mb-6">
              {plan.price === 0 ? "Free" : `$${plan.price}/mo`}
            </p>

            <button
              onClick={() => handlePlanClick(plan)}
              className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-2 rounded-lg transition"
            >
              {plan.price === 0 ? "Start for Free" : isSubscribed ? "Manage Subscription" : "Choose"}
            </button>
          </div>
        ))}
      </div>

      <footer className="mt-16 text-slate-500 text-sm">
        © {new Date().getFullYear()} ChipLoop – All rights reserved.
      </footer>
    </main>
  );
}

export default function LandingPage() {
  return (
    <Suspense fallback={<div className="text-white text-center mt-20">Loading...</div>}>
      <LandingPageContent />
    </Suspense>
  );
}
