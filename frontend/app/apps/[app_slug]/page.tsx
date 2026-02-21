"use client";

import { useEffect } from "react";
import { useRouter, useParams } from "next/navigation";

export default function AppSlugRouter() {
  const router = useRouter();
  const params = useParams<{ app_slug: string }>();
  const slug = params?.app_slug || "";

  useEffect(() => {
    if (!slug) return;

    const dedicated: Record<string, string> = {
      "validation-run": "/apps/validation-run",

      // ✅ NEW
      "arch2rtl": "/apps/arch2rtl",
      "integrate": "/apps/integrate",
      "dqa": "/apps/dqa",
      "verify": "/apps/verify",
      "smoke": "/apps/smoke",
    };

    const target = dedicated[slug];
    if (target) router.replace(target);
  }, [slug, router]);

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-4xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button
            className="rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700 transition"
            onClick={() => router.push("/apps")}
          >
            ← Back to Apps
          </button>
          <button
            className="rounded-xl border border-slate-700 px-4 py-2 hover:bg-slate-900 transition"
            onClick={() => router.push("/workflow")}
          >
            Studio
          </button>
        </div>

        <div className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">Generic App Runner</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">{slug || "unknown"}</h1>
          <p className="mt-3 text-slate-300">
            This app doesn’t have a dedicated page yet.
          </p>
        </div>
      </div>
    </main>
  );
}



