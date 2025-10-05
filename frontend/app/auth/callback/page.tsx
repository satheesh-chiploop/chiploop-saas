"use client";

import { Suspense, useEffect } from "react";
import { useRouter, useSearchParams } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

// ✅ Inner component (can safely use useSearchParams)
function CallbackContent() {
  const router = useRouter();
  const searchParams = useSearchParams();

  useEffect(() => {
    const handleRedirect = async () => {
      const { data: { session } } = await supabase.auth.getSession();

      if (session) {
        const next = searchParams.get("next");
        router.replace(next || "/workflow");
      } else {
        router.replace("/login");
      }
    };

    handleRedirect();
  }, [router, searchParams]);

  return <p>Completing sign-in…</p>;
}

// ✅ Outer component wraps it in Suspense (Next.js requirement)
export default function CallbackPage() {
  return (
    <Suspense fallback={<p>Loading callback...</p>}>
      <CallbackContent />
    </Suspense>
  );
}
