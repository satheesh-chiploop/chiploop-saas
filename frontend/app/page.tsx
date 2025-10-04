"use client";

import { useRouter, useSearchParams } from "next/navigation";
import { useState, useEffect, Suspense } from "react";
import { createClient } from "@supabase/supabase-js";
const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);
function LandingPageContent() {
  const router = useRouter();
  const searchParams = useSearchParams();
  const [isStudent, setIsStudent] = useState(false);
  const [isSubscribed, setIsSubscribed] = useState(false); // ✅ new state

  const portal = searchParams.get("portal");

  // ✅ Check subscription status based on Supabase email
  useEffect(() => {
    const checkSubscription = async () => {
      try {
        const token = localStorage.getItem("supabase.auth.token");
        if (!token) return;

        const parsed = JSON.parse(token);
        const userEmail = parsed?.currentSession?.user?.email;
        if (!userEmail) return;

        const res = await fetch(`/api/check-subscription?email=${userEmail}`);
        const data = await res.json();
        if (data.status === "active") {
          setIsSubscribed(true);
        }
      } catch (err) {
        console.error("❌ Subscription check failed", err);
      }
    };

    checkSubscription();
  }, []);

  const plans = [
    { name: "Freemium", desc: "1 agent, 1 workflow, free trial", price: 0 },
    { name: "Basic", desc: "10 agents, 5 workflows", price: 9.99 },
    { name: "Pro", desc: "30 agents, 20 workflows", price: 19.99 },
    { name: "Enterprise", desc: "Unlimited agents/workflows", price: 249.99 },
  ];

  const getPrice = (price: number) =>
    price === 0 ? "Free" : isStudent ? `$${(price / 2).toFixed(2)}/mo` : `$${price}/mo`;

  return (
    <main className="flex flex-col items-center justify-center min-h-screen bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white px-6">
      {portal === "success" && (
        <div className="mb-6 p-3 rounded-lg bg-green-100 text-green-700 font-medium">
          🎉 Subscription updated successfully!
        </div>
      )}

      {/* Hero */}
      <h1 className="text-5xl font-extrabold text-cyan-400 mb-6 text-center">
        Welcome to ChipLoop
      </h1>
      <p className="text-lg text-slate-300 max-w-2xl text-center mb-8">
        Agentic AI platform to create, manage, and execute AI agents and workflows effortlessly.
      </p>

      {/* CTA */}
      <div className="flex gap-4 mb-12">
        <button
          onClick={() => router.push("/workflow")}
          className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-3 rounded-xl shadow-lg transition"
        >
          🚀 Start Now
        </button>
        <button
          onClick={() => router.push("/login")}
          className="bg-slate-700 hover:bg-slate-600 text-white font-bold px-6 py-3 rounded-xl shadow-lg transition"
        >
          🔑 Login
        </button>
      </div>

      {/* Why ChipLoop / Use ChipLoop */}
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
          <div>
            <h3 className="text-xl font-bold mb-4">Use ChipLoop</h3>
            <ul className="space-y-2 text-slate-300">
              <li>🔧 Drag & drop agents into workflows</li>
              <li>📑 Run prebuilt workflows or create your own</li>
              <li>💾 Save and load workflows to your account</li>
              <li>🤖 Create your own custom AI agents</li>
            </ul>
          </div>
        </div>
      </div>

      {/* ✅ Manage Subscription (visible only if subscribed) */}
      {isSubscribed && (
        <div className="mt-10 text-center">
          <button
            onClick={async () => {
              try {
                const res = await fetch("/api/create-customer-portal-session", { method: "POST" });
                const data = await res.json();
                if (data.url) window.location.href = data.url;
                else alert("❌ Failed to open customer portal");
              } catch (err) {
                console.error("Portal session error:", err);
              }
            }}
            className="bg-yellow-400 hover:bg-yellow-300 text-black font-bold px-6 py-3 rounded-lg shadow-lg transition"
          >
            ⚙️ Manage Subscription
          </button>
        </div>
      )}

      {/* Pricing Section */}
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
            <div key={plan.name} className="p-6 bg-slate-800 rounded-xl shadow-lg flex flex-col justify-between">
              <h4 className="font-bold text-xl mb-2">{plan.name}</h4>
              <p className="text-slate-300 mb-4">{plan.desc}</p>
              <p className="text-cyan-400 font-bold text-2xl mb-4">{getPrice(plan.price)}</p>
              <button
                  onClick={async () => {
                      if (plan.price === 0) {
                        router.push("/login");
                      } else {
                        try {
                           const { data: { session } } = await supabase.auth.getSession();
                           const userId = session?.user?.id || "unknown";

                          const res = await fetch("/api/create-checkout-session", {
                              method: "POST",
                              headers: { "Content-Type": "application/json" },
                              body: JSON.stringify({
                                  plan: plan.name,
                                  user_id: userId, // ✅ send user ID
                              }),
                          });

                          const { url, error } = await res.json();
                          if (url) {
                             window.location.assign(url);
                          } else {
                             console.error("Checkout error:", error);
                             alert("❌ Failed to start checkout");
                          }
                     } catch (err) {
                       console.error("Checkout exception:", err);
                       alert("❌ Checkout failed");
                     }
                   }
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
