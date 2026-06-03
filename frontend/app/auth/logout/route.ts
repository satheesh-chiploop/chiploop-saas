import { NextResponse } from "next/server";

export async function POST() {
  const response = NextResponse.json({ status: "signed_out" });
  response.cookies.set("chiploop_access_token", "", { httpOnly: true, secure: process.env.NODE_ENV === "production", sameSite: "lax", maxAge: 0, path: "/" });
  response.cookies.set("chiploop_id_token", "", { httpOnly: true, secure: process.env.NODE_ENV === "production", sameSite: "lax", maxAge: 0, path: "/" });
  return response;
}
