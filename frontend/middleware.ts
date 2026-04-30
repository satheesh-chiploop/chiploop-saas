import { NextResponse, type NextRequest } from "next/server";
import { createMiddlewareClient } from "@supabase/auth-helpers-nextjs";

export async function middleware(req: NextRequest) {
  const res = NextResponse.next();

  // Avoid caching protected pages to prevent stale authenticated HTML.
  res.headers.set("Cache-Control", "no-store, no-cache, must-revalidate, proxy-revalidate");
  res.headers.set("Pragma", "no-cache");
  res.headers.set("Expires", "0");

  const supabase = createMiddlewareClient({ req, res });

  const {
    data: { session },
  } = await supabase.auth.getSession();

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

