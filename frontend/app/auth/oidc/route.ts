import crypto from "crypto";
import { NextResponse } from "next/server";

function base64url(value: Buffer): string {
  return value.toString("base64").replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
}

export async function GET(request: Request) {
  const requestUrl = new URL(request.url);
  const issuer = (process.env.CHIPLOOP_OIDC_ISSUER || "").replace(/\/$/, "");
  const clientId = process.env.CHIPLOOP_OIDC_CLIENT_ID || "";
  const authorizationEndpoint = process.env.CHIPLOOP_OIDC_AUTHORIZATION_ENDPOINT || `${issuer}/authorize`;
  if (!issuer || !clientId) {
    return NextResponse.redirect(`${requestUrl.origin}/login?error=oidc_not_configured`);
  }

  const next = requestUrl.searchParams.get("next") || "/apps";
  const state = base64url(crypto.randomBytes(24));
  const verifier = base64url(crypto.randomBytes(48));
  const challenge = base64url(crypto.createHash("sha256").update(verifier).digest());
  const redirectUri = `${requestUrl.origin}/auth/callback`;
  const url = new URL(authorizationEndpoint);
  url.searchParams.set("client_id", clientId);
  url.searchParams.set("response_type", "code");
  url.searchParams.set("redirect_uri", redirectUri);
  url.searchParams.set("scope", process.env.CHIPLOOP_OIDC_SCOPE || "openid profile email");
  url.searchParams.set("state", state);
  url.searchParams.set("code_challenge", challenge);
  url.searchParams.set("code_challenge_method", "S256");

  const response = NextResponse.redirect(url);
  const secure = process.env.NODE_ENV === "production";
  response.cookies.set("chiploop_oidc_state", state, { httpOnly: true, secure, sameSite: "lax", maxAge: 600, path: "/" });
  response.cookies.set("chiploop_oidc_verifier", verifier, { httpOnly: true, secure, sameSite: "lax", maxAge: 600, path: "/" });
  response.cookies.set("chiploop_oidc_next", next.startsWith("/") ? next : "/apps", { httpOnly: true, secure, sameSite: "lax", maxAge: 600, path: "/" });
  return response;
}
