

// route.ts

import { NextResponse } from "next/server";
import { cookies } from "next/headers";
import { createRouteHandlerClient } from "@supabase/auth-helpers-nextjs";

export async function GET(request: Request) {
  const requestUrl = new URL(request.url);
  const code = requestUrl.searchParams.get("code");
  const next = requestUrl.searchParams.get("next") || "/apps";
  const platformProvider = (process.env.NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER || "supabase").toLowerCase();

  if (platformProvider === "backend") {
    const cookieStore = await cookies();
    const state = requestUrl.searchParams.get("state") || "";
    const expectedState = cookieStore.get("chiploop_oidc_state")?.value || "";
    const verifier = cookieStore.get("chiploop_oidc_verifier")?.value || "";
    const oidcNext = cookieStore.get("chiploop_oidc_next")?.value || "/apps";
    if (!code || !state || state !== expectedState || !verifier) {
      return NextResponse.redirect(`${requestUrl.origin}/login?error=auth_failed`);
    }
    const issuer = (process.env.CHIPLOOP_OIDC_ISSUER || "").replace(/\/$/, "");
    const tokenEndpoint = process.env.CHIPLOOP_OIDC_TOKEN_ENDPOINT || `${issuer}/token`;
    const body = new URLSearchParams({
      grant_type: "authorization_code",
      code,
      client_id: process.env.CHIPLOOP_OIDC_CLIENT_ID || "",
      redirect_uri: `${requestUrl.origin}/auth/callback`,
      code_verifier: verifier,
    });
    if (process.env.CHIPLOOP_OIDC_CLIENT_SECRET) body.set("client_secret", process.env.CHIPLOOP_OIDC_CLIENT_SECRET);
    const tokenResponse = await fetch(tokenEndpoint, {
      method: "POST",
      headers: { "Content-Type": "application/x-www-form-urlencoded" },
      body,
      cache: "no-store",
    });
    if (!tokenResponse.ok) {
      return NextResponse.redirect(`${requestUrl.origin}/login?error=auth_failed`);
    }
    const tokens = await tokenResponse.json();
    const redirectTo = oidcNext.startsWith("/") ? oidcNext : "/apps";
    const response = NextResponse.redirect(`${requestUrl.origin}${redirectTo}`);
    const secure = process.env.NODE_ENV === "production";
    response.cookies.set("chiploop_access_token", String(tokens.access_token || ""), {
      httpOnly: true, secure, sameSite: "lax", maxAge: Number(tokens.expires_in || 3600), path: "/",
    });
    if (tokens.id_token) {
      response.cookies.set("chiploop_id_token", String(tokens.id_token), {
        httpOnly: true, secure, sameSite: "lax", maxAge: Number(tokens.expires_in || 3600), path: "/",
      });
    }
    response.cookies.delete("chiploop_oidc_state");
    response.cookies.delete("chiploop_oidc_verifier");
    response.cookies.delete("chiploop_oidc_next");
    return response;
  }

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

