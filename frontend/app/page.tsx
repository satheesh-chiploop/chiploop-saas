"use client";

import { useRouter } from "next/navigation";
import { useEffect, useState, Suspense } from "react";
import { createClient } from "@supabase/supabase-js";

// ✅ Supabase init
const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

function LandingPageContent() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);

  // ✅ Get Supabase session
  useEffect(() => {
    const getSession = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      const email = session?.user?.email || null;
      setUserEmail(email);
    };
    getSession();
  }, []);

  // ✅ Handle Login/Workflow button
  const handleMainButton = () => {
    if (userEmail) router.push("/workflow");
    else router.push("/login");
  };

  return (
    <main className="min-h-screen flex flex-col items-center justify-between bg-gradient-to-br from-slate-900 via-slate-950 to-black text-white">
      
      {/* 🧭 Top Navigation */}
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
          <button onClick={() => router.push("/academy")} className="hover:text-cyan-400 transition">
            Academy
          </button>
          <button onClick={() => router.push("/pricing")} className="hover:text-cyan-400 transition">
            Pricing
          </button>
        </div>
        <div>
          <button
            onClick={handleMainButton}
            className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-5 py-2 rounded-lg shadow-lg"
          >
            {userEmail ? "🚀 Go to Workflow" : "🔑 Login"}
          </button>
        </div>
      </nav>

      {/* 🚀 Hero Section */}
      <section className="flex flex-col items-center justify-center text-center px-6 mt-32 mb-16">
        <h1 className="text-5xl md:text-6xl font-extrabold text-white mb-6">
          Build, Automate, and Orchestrate
          <br /> Chip Design Workflows
        </h1>
        <p className="text-lg text-slate-300 max-w-3xl mb-10">
          An Agentic AI Platform unifying Digital, Analog and Embedded Loops in one platform.
        </p>
        <button
          onClick={handleMainButton}
          className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-8 py-3 rounded-xl shadow-lg transition"
        >
          Get Started
        </button>
      </section>

      {/* 💠 Loops Section */}
      <section className="w-full max-w-6xl px-6 mb-16 text-center">
        <div className="grid grid-cols-1 md:grid-cols-3 gap-8">
          {[
            {
              name: "Digital Loop",
              desc: "Accelerate digital design and verification",
              icon: "💻",
            },
            {
              name: "Analog Loop",
              desc: "Automate analog circuit optimization",
              icon: "⚙️",
            },
            {
              name: "Embedded Loop",
              desc: "Streamline embedded systems development",
              icon: "📶",
            },
            {
              name: "Validation Loop",
              desc: "Automate Hardware/Lab testing/validation",
              icon: "📶",
            },
          ].map((loop) => (
            <div
              key={loop.name}
              className="p-8 bg-slate-800/70 rounded-xl shadow-lg hover:bg-slate-700 transition"
            >
              <div className="text-5xl mb-3">{loop.icon}</div>
              <h4 className="font-bold text-2xl mb-3 text-cyan-400">{loop.name}</h4>
              <p className="text-slate-300 mb-5">{loop.desc}</p>
              <button
                onClick={handleMainButton}
                className="border border-cyan-400 text-cyan-400 hover:bg-cyan-500 hover:text-black px-5 py-2 rounded-lg transition"
              >
                Explore
              </button>
            </div>
          ))}
        </div>
      </section>

      {/* ⚡ Agentic AI Tagline */}
      <section className="w-full max-w-4xl text-center mb-16">
        <div className="bg-slate-800/70 text-cyan-400 py-4 rounded-xl font-semibold shadow-lg flex items-center justify-center gap-2">
          ⚡ Agentic AI at the Core of Every Loop
        </div>
      </section>

      {/* 🧩 Testimonials + Use Cases */}
      <section className="w-full max-w-6xl grid grid-cols-1 md:grid-cols-2 gap-8 px-6 mb-20">
        <div className="p-6 bg-slate-800/70 rounded-xl shadow-lg">
          <h3 className="text-xl font-bold mb-4 text-cyan-400">Testimonials</h3>
          <p className="text-slate-300">
            Used by Engineers at Analog Devices, Broadcom, and Universities worldwide.
          </p>
        </div>
        <div className="p-6 bg-slate-800/70 rounded-xl shadow-lg">
          <h3 className="text-xl font-bold mb-4 text-cyan-400">Use Cases</h3>
          <p className="text-slate-300">
            From RTL verification to mixed-signal simulation — ChipLoop unifies your entire flow.
          </p>
        </div>
      </section>

      {/* 📞 Footer */}
      <footer className="w-full border-t border-slate-800 py-8 text-center text-slate-400 text-sm bg-black/70">
        <div className="mb-4">
          <button
            onClick={() => router.push("/pricing")}
            className="bg-cyan-500 hover:bg-cyan-400 text-black font-bold px-6 py-2 rounded-lg shadow"
          >
            Book a Demo
          </button>
        </div>
        <p>© 2025 ChipLoop | Built with ❤️ by Satheesh Pillai</p>
        <div className="mt-2 space-x-4 text-slate-500">
          <button onClick={() => router.push("/contact")}>Contact</button>
          <button onClick={() => router.push("/careers")}>Careers</button>
          <button onClick={() => router.push("/privacy")}>Privacy</button>
          <button onClick={() => router.push("/terms")}>Terms</button>
        </div>
      </footer>
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
