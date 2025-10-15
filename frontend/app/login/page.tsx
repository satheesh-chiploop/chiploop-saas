"use client";

import React, { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import toast, { Toaster } from "react-hot-toast";
import { FcGoogle } from "react-icons/fc";
import { FaGithub } from "react-icons/fa";

export default function LoginPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();

  const [email, setEmail] = useState("");
  const [password, setPassword] = useState("");
  const [loading, setLoading] = useState(false);
  const [mode, setMode] = useState<"signin" | "signup">("signin");

  // 🔹 Redirect to workflow if already logged in
  useEffect(() => {
    (async () => {
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (session) router.push("/workflow");
    })();
  }, [supabase, router]);

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
          options: { emailRedirectTo: `${window.location.origin}/auth/callback` },
        });
      } else {
        result = await supabase.auth.signInWithPassword({ email, password });
      }

      if (result.error) throw result.error;

      toast.success(
        mode === "signup"
          ? "✅ Account created! Check your email to confirm."
          : "✅ Welcome back!"
      );
      if (mode === "signin") router.push("/workflow");
    } catch (error: any) {
      toast.error(error.message || "Something went wrong.");
    } finally {
      setLoading(false);
    }
  };

  // 🔹 OAuth login (Google/GitHub)
  const handleOAuth = async (provider: "google" | "github") => {
    const { error } = await supabase.auth.signInWithOAuth({
      provider,
      options: { redirectTo: `${window.location.origin}/auth/callback` },
    });
    if (error) toast.error(error.message);
  };

  // 🔹 Magic Link
  const handleMagicLink = async () => {
    setLoading(true);
    const { error } = await supabase.auth.signInWithOtp({
      email,
      options: { emailRedirectTo: `${window.location.origin}/auth/callback` },
    });
    setLoading(false);
    if (error) toast.error(error.message);
    else toast.success("✅ Magic link sent! Check your inbox.");
  };

  return (
    <main className="min-h-screen flex flex-col justify-center items-center bg-[#0b0b0c] text-white">
      <Toaster position="top-center" reverseOrder={false} />
      <div className="bg-slate-900 border border-slate-700 p-8 rounded-2xl shadow-2xl w-96">
        <h1 className="text-3xl font-extrabold text-cyan-400 text-center mb-4">
          CHIPLOOP Login
        </h1>

        {/* Toggle between Sign In / Sign Up */}
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

        {/* Email form */}
        <form onSubmit={handleEmailAuth} className="flex flex-col space-y-4">
          <input
            type="email"
            placeholder="you@example.com"
            value={email}
            onChange={(e) => setEmail(e.target.value)}
            required
            className="px-4 py-2 rounded-md text-black focus:ring-2 focus:ring-cyan-400"
          />
          <input
            type="password"
            placeholder="Enter password"
            value={password}
            onChange={(e) => setPassword(e.target.value)}
            required
            className="px-4 py-2 rounded-md text-black focus:ring-2 focus:ring-cyan-400"
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
              ? "Create Account"
              : "Sign In"}
          </button>
        </form>

        {/* Magic link login */}
        <div className="mt-4 text-center text-sm text-gray-400">
          <button
            onClick={handleMagicLink}
            className="text-cyan-400 hover:underline"
          >
            Or send me a Magic Link
          </button>
        </div>

        {/* OAuth providers */}
        <div className="flex flex-col space-y-3 mt-6">
          <button
            onClick={() => handleOAuth("google")}
            className="flex items-center justify-center gap-3 bg-white text-black py-2 rounded-md hover:bg-gray-200"
          >
            <FcGoogle size={20} /> Continue with Google
          </button>
          <button
            onClick={() => handleOAuth("github")}
            className="flex items-center justify-center gap-3 bg-gray-800 text-white py-2 rounded-md hover:bg-gray-700"
          >
            <FaGithub size={20} /> Continue with GitHub
          </button>
        </div>
      </div>

      <p className="text-gray-500 text-xs mt-6">
        Secure login powered by Supabase Auth
      </p>
    </main>
  );
}
