import { NextResponse } from "next/server";

export async function GET(req: Request) {
  try {
    const { searchParams } = new URL(req.url);
    const email = searchParams.get("email");

    if (!email) {
      return NextResponse.json({ error: "Missing email parameter" }, { status: 400 });
    }

    const backendUrl = `http://209.38.74.151/check-subscription?email=${encodeURIComponent(email)}`;
    const res = await fetch(backendUrl);

    if (!res.ok) {
      throw new Error(`Backend error: ${res.status}`);
    }

    const data = await res.json();
    return NextResponse.json(data);
  } catch (err: any) {
    console.error("❌ check-subscription error:", err);
    return NextResponse.json({ error: err.message || "Server error" }, { status: 500 });
  }
}
