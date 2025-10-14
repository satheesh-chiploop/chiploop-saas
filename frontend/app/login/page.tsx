"use client";

import { useState } from "react";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { useRouter } from "next/navigation";
import toast, { Toaster } from "react-hot-toast";

export default function LoginPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const [email, setEmail] = useState("");
  const [password, setPassword] = useState("");
  const [loading, setLoading] = useState(false);

  const handleLogin = async (e: React.FormEvent) => {
    e.preventDefault();
    setLoading(true);
    try {
      const { data, error } = await supabase.auth.signInWithPassword({ email, password });
      if (error) throw error;

      toast.success("Welcome back!");
      setTimeout(() => router.push("/workflow"), 1000);
    } catch (err: any) {
      toast.error(err.message || "Login failed");
    } finally {
      setLoading(false);
    }
  };

  const handleSignUp = async () => {
    setLoading(true);
    try {
      const { data, error } = await supabase.auth.signUp({ email, password });
      if (error) throw error;
      toast.success("Check your inbox to confirm your email!");
    } catch (err: any) {
      toast.error(err.message || "Sign-up failed");
    } finally {
      setLoading(false);
    }
  };

  const handleMagicLink = async () => {
    try {
      const { error } = await supabase.auth.signInWithOtp({
        email,
        options: { emailRedirectTo: `${location.origin}/auth/callback` },
      });
      if (error) throw error;
      toast.success("Magic link sent to your email!");
    } catch (err: any) {
      toast.error(err.message || "Could not send magic link");
    }
  };

  const handleOAuth = async (provider: "github" | "google") => {
    try {
      const { data, error } = await supabase.auth.signInWithOAuth({
        provider,
        options: { redirectTo: `${location.origin}/auth/callback` },
      });
      if (error) throw error;
      toast("Redirecting to " + provider.toUpperCase() + "…");
    } catch (err: any) {
      toast.error(err.message || "OAuth login failed");
    }
  };

  return (
    <div className="min-h-screen flex items-center justify-center bg-black text-white">
      <Toaster position="top-right" />
      <div className="bg-neutral-900 border border-neutral-700 rounded-2xl shadow-lg p-8 w-full max-w-md">
        <h1 className="text-3xl font-bold mb-6 text-center text-cyan-400">
          Welcome to ChipLoop
        </h1>
        <form onSubmit={handleLogin} className="space-y-4">
          <div>
            <label className="block text-sm text-neutral-400 mb-1">Email</label>
            <input
              type="email"
              required
              value={email}
              onChange={(e) => setEmail(e.target.value)}
              className="w-full px-4 py-2 rounded-lg bg-neutral-800 border border-neutral-600 focus:border-cyan-400 focus:outline-none"
            />
          </div>
          <div>
            <label className="block text-sm text-neutral-400 mb-1">Password</label>
            <input
              type="password"
              required
              value={password}
              onChange={(e) => setPassword(e.target.value)}
              className="w-full px-4 py-2 rounded-lg bg-neutral-800 border border-neutral-600 focus:border-cyan-400 focus:outline-none"
            />
          </div>
          <button
            type="submit"
            disabled={loading}
            className="w-full bg-cyan-500 hover:bg-cyan-400 text-black font-semibold rounded-lg py-2 transition"
          >
            {loading ? "Signing in..." : "Sign In"}
          </button>
        </form>

        <div className="flex justify-between mt-4">
          <button
            onClick={handleSignUp}
            disabled={loading}
            className="text-sm text-cyan-300 hover:text-cyan-200"
          >
            Sign Up
          </button>
          <button
            onClick={handleMagicLink}
            className="text-sm text-yellow-300 hover:text-yellow-200"
          >
            Send Magic Link
          </button>
        </div>

        <div className="mt-6 border-t border-neutral-700 pt-4 text-center">
          <p className="text-neutral-400 text-sm mb-2">Or continue with</p>
          <div className="flex justify-center gap-3">
            <button
              onClick={() => handleOAuth("github")}
              className="bg-neutral-800 hover:bg-neutral-700 px-4 py-2 rounded-lg border border-neutral-600"
            >
              GitHub
            </button>
            <button
              onClick={() => handleOAuth("google")}
              className="bg-neutral-800 hover:bg-neutral-700 px-4 py-2 rounded-lg border border-neutral-600"
            >
              Google
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}
