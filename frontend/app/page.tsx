"use client";

import { useRouter, useSearchParams } from "next/navigation";
import { useState, useEffect, Suspense } from "react";
import { createClient } from "@supabase/supabase-js";

// ✅ Supabase init
const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

function LandingPageContent() {
  const router = useRouter();
  const searchParams = useSearchParams();
  const [isStudent, setIsStudent] = useState(false);
  const [isSubscribed, setIsSubscribed] = useState(false);
  const [userEmail, setUserEmail] = useState<string | null>(null);

  const portal = searchParams.get("portal");

  // ✅ Get Supabase user session
  useEffect(() => {
    const checkSession = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const email = session?.user?.email || null;
      setUserEmail(email);

      if (email) {
        try {
          const res = await fetch(`/api/check-subscription?email=${email}`);
          const data = await res.json();
          if (data.status === "active") setIsSubscribed(true);
        } catch (err) {
          console.error("❌ Subscription check failed", err);
        }
      }
    };
    checkSession();
  }, []);

  const plans = [
    { name: "Freemium", desc: "1 agent, 1 workflow, free trial", price: 0 },
    { name: "Basic", desc: "10 agents, 5 workflows", price: 9.99 },
    { name: "Pro", desc: "30 agents, 20 workflows", price: 19.99 },
    { name: "Enterprise", desc: "Unlimited agents/workflows", price: 249.99 },
  ];

  const getPrice = (price: number) =>
    price === 0 ? "Free" : isStudent ? `$${(price / 2).toFixed(2)}/mo` : `$${price}/mo`;

  // ✅ Stripe checkout
  const handleCheckout = async () => {
    try {
      const { data: { session } } = await supabase.auth.getSession();
      const token = session?.access_token;
      if (!token) {
        alert("⚠️ Please log in first.");
        router.push("/login");
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
      if (data.url) window.location.href = data.url;
      else alert("❌ Failed to start checkout");
    } catch (err) {
      console.error("Checkout error:", err);
      alert("❌ Error starting checkout");
    }
  };

  // ✅ Manage Subscription
  const handleManage = async () => {
    try {
      const res = await fetch("http://209.38.74.151/create-customer-portal-session", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ email: userEmail }),
      });
      const data = await res.json();
      if (data.url) window.location.href = data.url;
      else alert("❌ Failed to open customer portal");
    } catch (err) {
      console.error("Portal error:", err);
    }
  };

  return (
    <main className="flex flex-col items-center justify-center min-h-screen bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white px-6">
      {portal === "success" && (
        <div className="mb-6 p-3 rounded-lg bg-green-100 text-green-700 font-medium">
          🎉 Subscription updated successfully!
        </div>
      )}

      <h1 className="text-5xl font-extrabold text-cyan-400 mb-6 text-center">
        Welcome to ChipLoop
      </h1>
      <p className="text-lg text-slate-300 max-w-2xl text-center mb-8">
        Agentic AI platform to create, manage, and execute AI agents and workflows effortlessly.
      </p>

      {/* ✅ Auth actions */}
      <div className="flex gap-4 mb-12">
        {userEmail ? (
          <button
            onClick={() => router.push("/workflow")}
            className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-3 rounded-xl shadow-lg transition"
          >
            🚀 Go to Workflow
          </button>
        ) : (
          <button
            onClick={() => router.push("/login")}
            className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-3 rounded-xl shadow-lg transition"
          >
            🔑 Login
          </button>
        )}
      </div>

      {/* ✅ Manage Subscription (if logged in) */}
      {userEmail && (
        <button
          onClick={handleManage}
          className="bg-yellow-400 hover:bg-yellow-300 text-black font-bold px-6 py-3 rounded-lg shadow-lg transition mb-8"
        >
          ⚙️ Manage Subscription
        </button>
      )}

      {/* ✅ Why ChipLoop / Use ChipLoop */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-8 mt-6 w-full max-w-5xl">
        <div className="p-6 bg-slate-800 rounded-xl shadow-lg">
          <h3 className="text-xl font-bold mb-4">Why ChipLoop?</h3>
          <ul className="space-y-2 text-slate-300">
            <li>🚀 Faster chip design with AI</li>
            <li>🎓 Learn RTL & verification interactively</li>
            <li>🧩 Prebuilt agents & workflows</li>
            <li>🌍 Marketplace to build & sell chip AI workflows</li>
          </ul>
        </div>

        <div className="p-6 bg-slate-800 rounded-xl shadow-lg flex flex-col justify-between">
          <h3 className="text-xl font-bold mb-4">Use ChipLoop</h3>
          <ul className="space-y-2 text-slate-300">
            <li>🔧 Drag & drop agents into workflows</li>
            <li>📑 Run prebuilt workflows or create your own</li>
            <li>💾 Save and load workflows to your account</li>
            <li>🤖 Create your own custom AI agents</li>
          </ul>
        </div>
      </div>

      {/* ✅ Pricing */}
      <div className="mt-20 w-full max-w-4xl text-center">
        <h3 className="text-3xl font-bold mb-6">Pricing</h3>
        <div className="flex justify-center mb-6">
          <button
            onClick={() => setIsStudent(false)}
            className={`px-4 py-2 rounded-l-lg ${!isStudent ? "bg-cyan-500 text-black" : "bg-slate-700"}`}
          >
            Regular
          </button>
          <button
            onClick={() => setIsStudent(true)}
            className={`px-4 py-2 rounded-r-lg ${isStudent ? "bg-cyan-500 text-black" : "bg-slate-700"}`}
          >
            Student (50% off)
          </button>
        </div>

        <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
          {plans.map((plan) => (
            <div
              key={plan.name}
              className="p-6 bg-slate-800 rounded-xl shadow-lg flex flex-col justify-between"
            >
              <h4 className="font-bold text-xl mb-2">{plan.name}</h4>
              <p className="text-slate-300 mb-4">{plan.desc}</p>
              <p className="text-cyan-400 font-bold text-2xl mb-4">{getPrice(plan.price)}</p>
              <button
                onClick={() => {
                  if (plan.price === 0) router.push("/workflow");
                  else handleCheckout();
                }}
                className="bg-emerald-500 hover:bg-emerald-400 text-black font-bold py-2 px-4 rounded"
              >
                Choose
              </button>
            </div>
          ))}
        </div>
      </div>
    </main>
  );
}

export default function LandingPage() {
  return (
    <Suspense fallback={<div className="text-center p-10">Loading...</div>}>
      <LandingPageContent />
    </Suspense>
  );
}
