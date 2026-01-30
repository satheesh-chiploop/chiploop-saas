"use client";

import { useRouter, useParams } from "next/navigation";

export default function AppRunnerPlaceholder() {
  const router = useRouter();
  const params = useParams<{ app_slug: string }>();

  const slug = params?.app_slug || "unknown";

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="mx-auto max-w-4xl px-6 py-10">
        <div className="flex items-center justify-between">
          <button
            className="rounded-lg bg-slate-800 px-4 py-2 hover:bg-slate-700"
            onClick={() => router.push("/apps")}
          >
            ← Back to Apps
          </button>
          <button
            className="rounded-lg border border-slate-700 px-4 py-2 hover:bg-slate-900"
            onClick={() => router.push("/workflow")}
          >
            Studio
          </button>
        </div>

        <div className="mt-8 rounded-2xl border border-slate-800 bg-slate-900/30 p-6">
          <div className="text-sm text-slate-400">App</div>
          <h1 className="mt-2 text-3xl font-extrabold text-cyan-300">{slug}</h1>
          <p className="mt-3 text-slate-300">
            Runner UI will be wired here next (inputs upfront → one click → progress → outputs).
          </p>
        </div>
      </div>
    </main>
  );
}
