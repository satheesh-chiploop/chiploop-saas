"use client";

import { usePathname, useRouter } from "next/navigation";
import UpgradeNudge from "@/components/UpgradeNudge";
import TopNav from "@/components/TopNav";

const tabs = [
  { label: "Plan", href: "/settings/plan" },
  { label: "API Keys", href: "/settings/api-keys" },
  { label: "Usage", href: "/settings/usage" },
];

export default function SettingsNav({ children }: { children: React.ReactNode }) {
  const router = useRouter();
  const pathname = usePathname();
  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      <TopNav current="settings" showPlanBadge maxWidthClass="max-w-6xl" />

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


