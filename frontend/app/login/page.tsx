"use client";

import React, { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient, usesBackendPlatform } from "@/lib/platformClient";
import toast, { Toaster } from "react-hot-toast";

export default function LoginPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const backendPlatform = usesBackendPlatform();

  const [email, setEmail] = useState("");
  const [password, setPassword] = useState("");
  const [loading, setLoading] = useState(false);
  const [mode, setMode] = useState<"signin" | "signup">("signin");
  const [trialIntent, setTrialIntent] = useState(false);

  // ✅ NEW: prevent flash by waiting until auth is checked
  const [authChecked, setAuthChecked] = useState(false);

  const getNext = () => {
    if (typeof window === "undefined") return "/apps";
    const next = new URLSearchParams(window.location.search).get("next");
    return next && next.startsWith("/") ? next : "/apps";
  };

  useEffect(() => {
    let mounted = true;
  
    (async () => {
      const { data: { user } } = await supabase.auth.getUser();
      if (!mounted) return;
  
      const params = new URLSearchParams(window.location.search);
      if (params.get("mode") === "signup") setMode("signup");
      if (params.get("trial") === "1") setTrialIntent(true);

      setAuthChecked(true);
  
      if (user) router.replace(getNext());
    })();
  
    return () => {
      mounted = false;
    };
  }, [supabase, router]);
  
  
  // ✅ NEW: show a lightweight loading screen until session is known
  if (!authChecked) {
    return (
      <main className="min-h-screen flex flex-col justify-center items-center bg-[#0b0b0c] text-white">
        <div className="text-slate-300">Checking session...</div>
      </main>
    );
  }

  // 🔹 Email/Password sign-in or sign-up
  const handleEmailAuth = async (e: React.FormEvent) => {
    e.preventDefault();
    setLoading(true);

    try {
      let result;
      if (mode === "signup") {
        result = await supabase.auth.signUp({
          email,
          password,
          // ✅ small improvement: keep consistent apps-first landing after confirm
          options: {
            emailRedirectTo: `${window.location.origin}/auth/callback?next=${encodeURIComponent(getNext())}`,
          },
        });
      } else {
        result = await supabase.auth.signInWithPassword({ email, password });
      }

      if (result.error) throw result.error;

      toast.success(
        mode === "signup"
          ? trialIntent
            ? "Account created. Complete Stripe trial checkout to start your 3-day trial."
            : "Account created! Check your email to confirm."
          : "Welcome back!"
      );

      if (mode === "signin") router.replace(getNext()); // ✅ replace
    } catch (error: unknown) {
      const message = error instanceof Error ? error.message : "Something went wrong.";
      toast.error(message);
    } finally {
      setLoading(false);
    }
  };

  

  // 🔹 Magic Link
  const handleMagicLink = async () => {
    setLoading(true);
    const { error } = await supabase.auth.signInWithOtp({
      email,
      // ✅ small improvement: apps-first return
      options: { emailRedirectTo: `${window.location.origin}/auth/callback?next=${encodeURIComponent(getNext())}` },
    });
    setLoading(false);
    if (error) toast.error(error.message);
    else toast.success("Magic link sent. Check your inbox.");
  };

  const handleOidcLogin = () => {
    window.location.href = `/auth/oidc?next=${encodeURIComponent(getNext())}`;
  };

  return (
    <main className="min-h-screen flex flex-col justify-center items-center bg-[#0b0b0c] text-white">
      <Toaster position="top-center" reverseOrder={false} />
      <div className="bg-slate-900 border border-slate-700 p-8 rounded-2xl shadow-2xl w-96">
        <h1 className="text-3xl font-extrabold text-cyan-400 text-center mb-4">
          {mode === "signup" && trialIntent ? "Start ChipLoop 3-Day Trial" : "ChipLoop Login"}
        </h1>

        {backendPlatform ? (
          <button
            onClick={handleOidcLogin}
            className="w-full rounded-md bg-cyan-500 px-4 py-3 font-semibold text-black transition hover:bg-cyan-400"
          >
            Sign in with company identity
          </button>
        ) : null}

        {/* Toggle between Sign In / Sign Up */}
        {!backendPlatform ? (
        <>
        <div className="flex justify-center mb-6 space-x-4">
          <button
            onClick={() => setMode("signin")}
            className={`px-4 py-2 rounded-md font-semibold ${
              mode === "signin"
                ? "bg-cyan-500 text-black"
                : "bg-slate-800 text-gray-300"
            }`}
          >
            Sign In
          </button>
          <button
            onClick={() => setMode("signup")}
            className={`px-4 py-2 rounded-md font-semibold ${
              mode === "signup"
                ? "bg-cyan-500 text-black"
                : "bg-slate-800 text-gray-300"
            }`}
          >
            Sign Up
          </button>
        </div>

        {mode === "signup" && trialIntent ? (
          <div className="mb-5 rounded-lg border border-cyan-700/60 bg-cyan-950/30 p-3 text-sm text-cyan-100">
            Free 3-day trial. Starter is $19.99/month after 3 days. Billing is handled securely by Stripe. Cancel anytime before trial ends.
          </div>
        ) : null}

        {/* Email form */}
        <form onSubmit={handleEmailAuth} className="flex flex-col space-y-4">
          <input
            type="email"
            placeholder="you@example.com"
            value={email}
            onChange={(e) => setEmail(e.target.value)}
            required
            className="px-4 py-2 rounded-md border border-slate-700 bg-slate-950 text-white placeholder:text-slate-500 outline-none focus:ring-2 focus:ring-cyan-400"
          />
          <input
            type="password"
            placeholder="Enter password"
            value={password}
            onChange={(e) => setPassword(e.target.value)}
            required
            className="px-4 py-2 rounded-md border border-slate-700 bg-slate-950 text-white placeholder:text-slate-500 outline-none focus:ring-2 focus:ring-cyan-400"
          />

          <button
            type="submit"
            disabled={loading}
            className={`w-full py-2 rounded-md font-semibold transition ${
              loading
                ? "bg-gray-500 cursor-not-allowed"
                : "bg-cyan-500 hover:bg-cyan-400 text-black"
            }`}
          >
            {loading
              ? mode === "signup"
                ? "Creating..."
                : "Signing in..."
              : mode === "signup"
              ? trialIntent ? "Start free trial" : "Create Account"
              : "Sign In"}
          </button>
        </form>
        </>
        ) : null}

        {/* Magic link login */}
        {!backendPlatform ? (
        <div className="mt-4 text-center text-sm text-gray-400">
          <button
            onClick={handleMagicLink}
            className="text-cyan-400 hover:underline"
          >
            Or send me a Magic Link
          </button>
        </div>
        ) : null}

        
      </div>

      <p className="text-gray-500 text-xs mt-6">
        {backendPlatform ? "Secure login powered by your company identity provider." : "Secure login powered by Supabase Auth. Trial billing is handled by Stripe."}
      </p>
    </main>
  );
}



