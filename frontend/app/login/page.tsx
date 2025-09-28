"use client";
import { useRouter } from "next/navigation";
import { useState } from "react";

export default function LoginPage() {
  const [email, setEmail] = useState("");
  const [password, setPassword] = useState("");
  const router = useRouter();

  const handleLogin = () => {
    if (!email || !password) {
      alert("Please enter both email and password");
      return;
    }
    // For MVP: accept any email/password
    localStorage.setItem("chiploop_user", email);
    router.push("/workflow");
  };

  return (
    <div className="h-screen flex items-center justify-center bg-slate-900 text-white">
      <div className="p-8 bg-slate-800 rounded-lg shadow-lg w-96">
        <h1 className="text-2xl font-bold mb-4">Login</h1>
        <input
          type="email"
          placeholder="Email"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-700"
        />
        <input
          type="password"
          placeholder="Password"
          value={password}
          onChange={(e) => setPassword(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-700"
        />
        <button
          onClick={handleLogin}
          className="w-full bg-cyan-500 hover:bg-cyan-400 text-black font-bold py-2 px-4 rounded"
        >
          Login
        </button>
      </div>
    </div>
  );
}
