"use client";

import { useRouter, useSearchParams } from "next/navigation";
import { useEffect } from "react";
import { createClient } from "@supabase/supabase-js";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

export default function CallbackPage() {
  const router = useRouter();
  const searchParams = useSearchParams();

  useEffect(() => {
    const redirectUser = async () => {
      // Wait a moment for Supabase session to set
      const { data: { session } } = await supabase.auth.getSession();

      if (session) {
        // Check for ?next= param to route back appropriately
        const next = searchParams.get("next");
        router.replace(next || "/workflow");
      } else {
        router.replace("/login");
      }
    };

    redirectUser();
  }, [router, searchParams]);

  return <p>Completing sign-in…</p>;
}
