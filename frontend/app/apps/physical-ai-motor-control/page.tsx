"use client";

import { useEffect } from "react";
import { useRouter } from "next/navigation";

export default function PhysicalAiMotorControlRedirectPage() {
  const router = useRouter();
  useEffect(() => { router.replace("/apps/physical-ai?reference=motor"); }, [router]);
  return <main className="flex min-h-screen items-center justify-center bg-slate-950 text-slate-300">Opening the Physical AI motor journey…</main>;
}
