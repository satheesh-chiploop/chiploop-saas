"use client";

import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";
import { usePathname, useRouter } from "next/navigation";
import UpgradeNudge from "@/components/UpgradeNudge";

const tabs = [
  { label: "Plan", href: "/settings/plan" },
  { label: "API Keys", href: "/settings/api-keys" },
  { label: "Usage", href: "/settings/usage" },
];

export default function SettingsNav({ children }: { children: React.ReactNode }) {
  const router = useRouter();
  const pathname = usePathname();
  const supabase = createClientComponentClient();

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button
            className="flex items-center gap-2 text-xl font-extrabold"
            onClick={() => router.push("/apps")}
          >
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">Settings</span>
          </button>

          <div className="flex items-center gap-3">
            <button
              onClick={() => router.push("/apps")}
              className="rounded-lg border border-slate-700 px-4 py-2 text-slate-300 transition hover:bg-slate-900"
            >
              Apps
            </button>
            <button
              onClick={() => router.push("/workflow")}
              className="rounded-lg border border-slate-700 px-4 py-2 text-slate-300 transition hover:bg-slate-900"
            >
              Studio
            </button>
            <button
              onClick={async () => {
                await supabase.auth.signOut();
                router.push("/");
              }}
              className="rounded-lg border border-slate-700 px-4 py-2 text-slate-300 transition hover:bg-slate-900"
            >
              Logout
            </button>
          </div>
        </div>
      </div>

      <section className="mx-auto max-w-6xl px-6 py-8">
        <div className="mb-6 flex flex-wrap items-center justify-between gap-4">
          <div>
            <h1 className="text-3xl font-extrabold">Settings</h1>
            <p className="mt-2 text-sm text-slate-400">
              Plan, developer access, and usage for SDK and CLI workflows.
            </p>
          </div>

          <div className="flex rounded-lg border border-slate-800 bg-slate-950/70 p-1">
            {tabs.map((tab) => {
              const active = pathname === tab.href;
              return (
                <button
                  key={tab.href}
                  onClick={() => router.push(tab.href)}
                  className={`rounded-md px-4 py-2 text-sm transition ${
                    active
                      ? "bg-cyan-700 text-white"
                      : "text-slate-300 hover:bg-slate-900"
                  }`}
                >
                  {tab.label}
                </button>
              );
            })}
          </div>
        </div>

        <UpgradeNudge />
        {children}
      </section>
    </main>
  );
}


