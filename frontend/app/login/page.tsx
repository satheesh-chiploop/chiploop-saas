import { NextResponse } from "next/server";
import { cookies } from "next/headers";
import { createRouteHandlerClient } from "@supabase/auth-helpers-nextjs";

export async function GET(request: Request) {
  const url = new URL(request.url);
  const code = url.searchParams.get("code");
  const supabase = createRouteHandlerClient({ cookies });

  if (code) {
    // Perform session exchange and wait for cookies to commit
    await supabase.auth.exchangeCodeForSession(code);
    await new Promise((r) => setTimeout(r, 500));
  }

  // ✅ Redirect using 302 instead of 307 to force a new client request
  return NextResponse.redirect(`${url.origin}/workflow`, { status: 302 });
}
