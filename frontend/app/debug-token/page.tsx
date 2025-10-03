"use client";
import { useEffect, useState } from "react";
import { supabase } from "@/lib/supabaseClient";

export default function DebugToken() {
  const [token, setToken] = useState<string>("Loading...");

  useEffect(() => {
    const fetchToken = async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (session?.access_token) {
        setToken(session.access_token);
      } else {
        setToken("No token found (are you logged in?)");
      }
    };
    fetchToken();
  }, []);

  return (
    <div className="p-6 text-white bg-slate-900 h-screen">
      <h1 className="text-xl font-bold mb-4">Supabase Access Token</h1>
      <pre className="whitespace-pre-wrap break-all">{token}</pre>
    </div>
  );
}
