"use client";

import { useEffect, useState } from "react";
import { useRouter } from "next/navigation";
import { ApiClientError, apiGet } from "@/lib/apiClient";

type UpgradeHint = {
  show?: boolean;
  type?: string | null;
  target_plan?: string | null;
  message?: string;
};

type UpgradeStatusResponse = {
  status: string;
  upgrade_status?: {
    current_plan?: { display_name?: string; name?: string };
    trial_status?: string | null;
    days_remaining?: number | null;
    suggested_upgrade?: UpgradeHint;
  };
};

const STORAGE_KEY = "chiploop_upgrade_nudge_last_shown";
const COOLDOWN_MS = 6 * 60 * 60 * 1000;

function shouldShowNow(): boolean {
  if (typeof window === "undefined") return false;
  const raw = window.localStorage.getItem(STORAGE_KEY);
  if (!raw) return true;
  const last = Number(raw);
  return Number.isNaN(last) || Date.now() - last > COOLDOWN_MS;
}

export default function UpgradeNudge() {
  const router = useRouter();
  const [hint, setHint] = useState<UpgradeHint | null>(null);
  const [dismissed, setDismissed] = useState(false);
  const [showModal, setShowModal] = useState(false);

  useEffect(() => {
    let cancelled = false;
    async function loadStatus() {
      if (!shouldShowNow()) return;
      try {
        const data = await apiGet<UpgradeStatusResponse>("/settings/upgrade-status");
        const suggested = data.upgrade_status?.suggested_upgrade;
        if (!cancelled && suggested?.show) {
          setHint(suggested);
          window.localStorage.setItem(STORAGE_KEY, String(Date.now()));
        }
      } catch (error) {
        if (error instanceof ApiClientError && error.status === 401) return;
      }
    }
    loadStatus();
    return () => {
      cancelled = true;
    };
  }, []);

  if (!hint || dismissed) return null;

  const target = hint.target_plan || "Pro";
  const price = target === "Pro Max" ? "$44.99/month for first 3 months" : target === "Pro" ? "$29.99/month for first 3 months" : "$14.99/month for first 3 months";

  return (
    <>
    <div className="mb-5 rounded-lg border border-cyan-700/60 bg-cyan-950/30 p-4 text-sm text-cyan-100">
      <div className="flex flex-col gap-3 md:flex-row md:items-center md:justify-between">
        <div>
          <div className="font-semibold">{hint.type === "trial_expiring" ? "Trial reminder" : "Plan recommendation"}</div>
          <div className="mt-1 text-cyan-100/85">{hint.message || "A plan change may help with your current usage."}</div>
        </div>
        <div className="flex shrink-0 gap-2">
          <button
            onClick={() => setShowModal(true)}
            className="rounded-lg bg-cyan-600 px-3 py-2 text-xs font-bold text-white transition hover:bg-cyan-500"
          >
            Review upgrade
          </button>
          <button
            onClick={() => setDismissed(true)}
            className="rounded-lg border border-cyan-700/70 px-3 py-2 text-xs text-cyan-100 transition hover:bg-cyan-900/40"
          >
            Dismiss
          </button>
        </div>
      </div>
    </div>
    {showModal ? (
      <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/70 px-4">
        <div className="w-full max-w-md rounded-lg border border-slate-700 bg-slate-950 p-6 text-white shadow-2xl">
          <div className="text-lg font-bold">Upgrade recommendation</div>
          <p className="mt-2 text-sm text-slate-300">{hint.message}</p>
          <div className="mt-4 rounded-lg border border-slate-800 bg-black/30 p-4 text-sm">
            <div className="text-slate-400">Recommended plan</div>
            <div className="mt-1 text-2xl font-extrabold text-cyan-200">{target}</div>
            <div className="mt-1 text-cyan-100">{price}</div>
            <div className="mt-1 text-xs text-slate-400">25% off for the first 3 billing cycles.</div>
          </div>
          <div className="mt-5 flex justify-end gap-2">
            <button onClick={() => setShowModal(false)} className="rounded-lg border border-slate-700 px-4 py-2 text-sm text-slate-200 hover:bg-slate-900">Close</button>
            <button onClick={() => router.push("/pricing")} className="rounded-lg bg-cyan-600 px-4 py-2 text-sm font-bold text-white hover:bg-cyan-500">View pricing</button>
          </div>
        </div>
      </div>
    ) : null}
    </>
  );
}

