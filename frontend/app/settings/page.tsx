"use client";

import { useEffect } from "react";
import { useRouter } from "next/navigation";

export default function SettingsIndexPage() {
  const router = useRouter();

  useEffect(() => {
    router.replace("/settings/plan");
  }, [router]);

  return (
    <main className="flex min-h-screen items-center justify-center bg-black text-white">
      <div className="text-slate-300">Loading settings...</div>
    </main>
  );
}
