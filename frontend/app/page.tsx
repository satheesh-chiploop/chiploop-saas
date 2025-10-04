"use client";

import { useRouter } from "next/navigation";
import { useState } from "react";
import { useSearchParams } from "next/navigation";

export default function LandingPage() {
  const router = useRouter();
  const [isStudent, setIsStudent] = useState(false);

  // Pricing plans
  const plans = [
    { name: "Freemium", desc: "1 agent, 1 workflow, free trial", price: 0 },
    { name: "Basic", desc: "10 agents, 5 workflows", price: 9.99 },
    { name: "Pro", desc: "30 agents, 20 workflows", price: 19.99 },
    { name: "Enterprise", desc: "Unlimited agents/workflows", price: 249.99 },
  ];

  const getPrice = (price: number) => {
    if (price === 0) return "Free";
    return isStudent ? `$${(price / 2).toFixed(2)}/mo` : `$${price}/mo`;
  };

  return (
     const searchParams = useSearchParams();
     const portal = searchParams.get("portal");
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
        Agentic AI platform to create, manage, and execute AI agents and
        workflows effortlessly.
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

      {/* Two Boxes */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-8 mt-6 w-full max-w-5xl">
        {/* Why ChipLoop */}
        <div className="p-6 bg-slate-800 rounded-xl shadow-lg">
          <h3 className="text-xl font-bold mb-4">Why ChipLoop?</h3>
          <ul className="space-y-2 text-slate-300">
            <li>🚀 Faster chip design with AI</li>
            <li>🎓 Learn RTL & verification interactively</li>
            <li>🧩 Prebuilt agents & workflows</li>
            <li>🌍 Marketplace to build & sell chip AI workflows</li>
          </ul>
        </div>

        {/* Use ChipLoop */}
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

      {/* Pricing Section */}
      <div className="mt-20 w-full max-w-4xl text-center">
        <h3 className="text-3xl font-bold mb-6">Pricing</h3>
        <div className="flex justify-center mb-6">
          <button
            onClick={() => setIsStudent(false)}
            className={`px-4 py-2 rounded-l-lg ${
              !isStudent ? "bg-cyan-500 text-black" : "bg-slate-700"
            }`}
          >
            Regular
          </button>
          <button
            onClick={() => setIsStudent(true)}
            className={`px-4 py-2 rounded-r-lg ${
              isStudent ? "bg-cyan-500 text-black" : "bg-slate-700"
            }`}
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
              <p className="text-cyan-400 font-bold text-2xl mb-4">
                {getPrice(plan.price)}
              </p>
              <button
                 onClick={async () => {
                     if (plan.price === 0) {
                       router.push("/login"); // Freemium → just login
                     } else {
                       const res = await fetch("/api/create-checkout-session", {
                          method: "POST",
                          headers: { "Content-Type": "application/json" },
                          body: JSON.stringify({ plan: plan.name }), // optional: send which plan
                       });
                      const { url } = await res.json();
                      if (url) {
                          window.location.href = url; // redirect to Stripe Checkout
                      } else {
                          alert("❌ Failed to start checkout");
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
