"use client";

import React, { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import toast, { Toaster } from "react-hot-toast";

export default function LoginPage() {
  const router = useRouter();
  const supabase = createClientComponentClient();
  const [email, setEmail] = useState("");
  const [loading, setLoading] = useState(false);

  // 🔹 Redirect if already logged in
  useEffect(() => {
    (async () => {
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (session) router.push("/workflow");
    })();
  }, [supabase, router]);

  // 🔹 Handle Magic Link login
  const handleLogin = async (e: React.FormEvent) => {
    e.preventDefault();
    setLoading(true);

    const { error } = await supabase.auth.signInWithOtp({
      email,
      options: {
        emailRedirectTo: `${window.location.origin}/auth/callback`,
      },
    });

    setLoading(false);

    if (error) {
      toast.error(error.message);
    } else {
      toast.success("✅ Magic link sent! Check your email.");
    }
  };

  return (
    <main className="min-h-screen flex flex-col justify-center items-center bg-[#0b0b0c] text-white">
      <Toaster position="top-center" reverseOrder={false} />
      <h1 className="text-4xl font-extrabold text-cyan-400 mb-4">
        Welcome to CHIPLOOP
      </h1>
      <p className="text-gray-400 mb-8 text-center">
        Sign in with your email to access your workflows
      </p>

      <form
        onSubmit={handleLogin}
        className="bg-slate-900 border border-slate-700 p-8 rounded-2xl shadow-2xl w-80 flex flex-col space-y-4"
      >
        <input
          type="email"
          placeholder="you@example.com"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
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
          {loading ? "Sending..." : "Send Magic Link"}
        </button>
      </form>

      <p className="text-gray-500 text-sm mt-8">
        ⓘ Use your registered email to receive a secure login link.
      </p>
    </main>
  );
}
