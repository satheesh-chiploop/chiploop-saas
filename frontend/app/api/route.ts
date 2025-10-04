import { NextResponse } from "next/server";

export async function GET(req: Request): Promise<NextResponse> {
  try {
    const { searchParams } = new URL(req.url);
    const email = searchParams.get("email");

    if (!email) {
      return NextResponse.json(
        { error: "Missing email parameter" },
        { status: 400 }
      );
    }

    const backendUrl = `http://209.38.74.151/check-subscription?email=${encodeURIComponent(email)}`;
    const res = await fetch(backendUrl);

    if (!res.ok) {
      throw new Error(`Backend error: ${res.status}`);
    }

    // ✅ Properly type response JSON
    const data: { status?: string; error?: string } = await res.json();
    return NextResponse.json(data);
  } catch (err) {
    console.error("❌ check-subscription error:", err);
    const message =
      err instanceof Error ? err.message : "Unknown server error";
    return NextResponse.json({ error: message }, { status: 500 });
  }
}
