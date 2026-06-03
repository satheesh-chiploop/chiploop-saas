import { NextResponse, type NextRequest } from "next/server";
import { createMiddlewareClient } from "@supabase/auth-helpers-nextjs";

export async function middleware(req: NextRequest) {
  const res = NextResponse.next();

  // Avoid caching protected pages to prevent stale authenticated HTML.
  res.headers.set("Cache-Control", "no-store, no-cache, must-revalidate, proxy-revalidate");
  res.headers.set("Pragma", "no-cache");
  res.headers.set("Expires", "0");

  const backendPlatform = (process.env.NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER || "supabase").toLowerCase() === "backend";
  let session: unknown = null;
  if (backendPlatform) {
    session = req.cookies.get("chiploop_access_token")?.value || null;
  } else {
    const supabase = createMiddlewareClient({ req, res });
    const result = await supabase.auth.getSession();
    session = result.data.session;
  }

  const pathname = req.nextUrl.pathname;

  const isProtected =
    pathname.startsWith("/apps") ||
    pathname.startsWith("/workflow") ||
    pathname.startsWith("/settings") ||
    pathname.startsWith("/marketplace") ||
    pathname.startsWith("/admin");

  if (isProtected && !session) {
    const url = req.nextUrl.clone();
    url.pathname = "/login";
    url.searchParams.set("next", pathname);

    const redirectRes = NextResponse.redirect(url);
    redirectRes.headers.set(
      "Cache-Control",
      "no-store, no-cache, must-revalidate, proxy-revalidate"
    );
    redirectRes.headers.set("Pragma", "no-cache");
    redirectRes.headers.set("Expires", "0");
    return redirectRes;
  }

  return res;
}

export const config = {
  // Do not include /login here.
  matcher: ["/apps/:path*", "/workflow/:path*", "/settings/:path*", "/marketplace/:path*", "/admin/:path*"],
};

