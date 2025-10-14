import { createRouteHandlerClient } from "@supabase/auth-helpers-nextjs";
import { cookies } from "next/headers";
import { NextResponse } from "next/server";

// Spinner HTML (shown during redirect)
const spinnerHtml = `
<!DOCTYPE html>
<html lang="en">
<head><meta charset="UTF-8"><title>Logging in...</title></head>
<body style="background-color:black;color:white;display:flex;justify-content:center;align-items:center;height:100vh;font-family:sans-serif;">
  <div style="text-align:center;">
    <div style="border:4px solid #0ff;border-top:4px solid transparent;border-radius:50%;width:50px;height:50px;margin:auto;animation:spin 1s linear infinite;"></div>
    <p style="margin-top:1rem;">Verifying login...</p>
  </div>
  <style>@keyframes spin{0%{transform:rotate(0deg);}100%{transform:rotate(360deg);}}</style>
</body>
</html>
`;

export async function GET(request: Request) {
  const requestUrl = new URL(request.url);
  const code = requestUrl.searchParams.get("code");
  const supabase = createRouteHandlerClient({ cookies });

  if (code) {
    await supabase.auth.exchangeCodeForSession(code);
  }

  // Determine redirect based on existing workflows (simplified)
  let redirectUrl = "/workflow";
  try {
    const { data: workflows } = await supabase
      .from("workflows")
      .select("id")
      .limit(1);
    if (!workflows?.length) redirectUrl = "/pricing";
  } catch {
    // fallback
  }

  const response = NextResponse.redirect(`${requestUrl.origin}${redirectUrl}`);
  response.headers.set("Content-Type", "text/html");
  response.body = spinnerHtml;
  return response;
}
