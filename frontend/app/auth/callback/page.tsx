"use client";

import { Suspense, useEffect } from "react";
import { useRouter, useSearchParams } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

function CallbackContent() {
  const router = useRouter();
  const searchParams = useSearchParams();

  useEffect(() => {
    const redirect = async () => {
      const { data: { session } } = await supabase.auth.getSession();

      if (session) {
        // ✅ Always redirect to landing page after login/signup
        router.replace("/");
      } else {
        router.replace("/login");
      }
    };
    redirect();
  }, [router, searchParams]);

  return <p className="text-center p-10 text-white">Completing sign-in...</p>;
}

export default function CallbackPage() {
  return (
    <Suspense fallback={<p className="text-center text-white p-10">Loading callback...</p>}>
      <CallbackContent />
    </Suspense>
  );
}
