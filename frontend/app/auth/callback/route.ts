import { NextResponse } from "next/server";
import { cookies } from "next/headers";
import { createRouteHandlerClient } from "@supabase/auth-helpers-nextjs";

export async function GET(request: Request) {
  const requestUrl = new URL(request.url);
  const code = requestUrl.searchParams.get("code");
  const supabase = createRouteHandlerClient({ cookies });

  if (code) {
    try {
      // Exchange the code for a session and set cookies
      await supabase.auth.exchangeCodeForSession(code);
      await new Promise((r) => setTimeout(r, 500));
      console.log("✅ Supabase session created");
    } catch (error) {
      console.error("❌ Error exchanging session:", error);
      return NextResponse.redirect(`${requestUrl.origin}/login?error=auth_failed`);
    }
  }

  // ✅ Redirect to workflow page
  return NextResponse.redirect(`${requestUrl.origin}/workflow`);
}
