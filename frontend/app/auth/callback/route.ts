

// route.ts

import { NextResponse } from "next/server";
import { cookies } from "next/headers";
import { createRouteHandlerClient } from "@supabase/auth-helpers-nextjs";

export async function GET(request: Request) {
  const requestUrl = new URL(request.url);
  const code = requestUrl.searchParams.get("code");
  const next = requestUrl.searchParams.get("next") || "/apps";


  const supabase = createRouteHandlerClient({ cookies });

  if (code) {
    try {
      await supabase.auth.exchangeCodeForSession(code);
        console.log("✅ Supabase session established");
    } catch (err) {
      console.error("❌ Auth exchange failed", err);
      return NextResponse.redirect(
        `${requestUrl.origin}/login?error=auth_failed`
      );
    }
  }

  // ✅ SINGLE SOURCE OF TRUTH
  // Default → /apps
  const redirectTo = next.startsWith("/") ? next : "/apps";
  return NextResponse.redirect(`${requestUrl.origin}${redirectTo}`);
  
}

