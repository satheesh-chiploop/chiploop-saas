"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";

const supabase = createClient(
  process.env.NEXT_PUBLIC_SUPABASE_URL!,
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
);

type LoopType = "digital" | "validation" | "analog" | "embedded" | "system";

type AppCard = {
  slug: string;
  title: string;
  subtitle: string;
  loop_type: LoopType;
  status?: "Flagship" | "Coming";
  nudge?: "Recommended" | "Most used" | "New";
  promise?: string; // short outcome promise
};

const LOOP_META: Record<LoopType, { title: string; tagline: string; accent: string }> = {
  digital: { title: "Digital Loop", tagline: "Design → RTL → Verify → Improve", accent: "accent-digital" },
  validation: { title: "Validation Loop", tagline: "Plan → Run → Learn → Improve", accent: "accent-validation" },
  analog: { title: "Analog Loop", tagline: "Analyze → Simulate → Correlate → Improve", accent: "accent-analog" },
  embedded: { title: "Firmware Loop", tagline: "Code → Run → Observe → Fix", accent: "accent-embedded" },
  system: { title: "System Loop", tagline: "Integrate → Analyze → Optimize", accent: "accent-system" },
};

export default function AppsHomePage() {
  const router = useRouter();
  const [userEmail, setUserEmail] = useState<string | null>(null);

  // ✅ MINIMAL ADD: stop flashing by gating redirects until auth is known
  const [authChecked, setAuthChecked] = useState(false);
  const [isAuthed, setIsAuthed] = useState(false);

  // A tiny “choice architecture” state: keep UI simple by defaulting to Recommended
  const [view, setView] = useState<"recommended" | "all">("recommended");


  useEffect(() => {
    let mounted = true;

    (async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (!mounted) return;

      setAuthChecked(true);

      // Middleware should prevent this, but keep as safety net
      if (!session) {
        router.replace("/login?next=/apps");
        return;
      }

      setIsAuthed(true);
      setUserEmail(session.user.email ?? null);
    })();

    const { data: sub } = supabase.auth.onAuthStateChange((_event, session) => {
      if (!mounted) return;
      if (!session) {
        setIsAuthed(false);
        router.replace("/login?next=/apps");
        return;
      }
      setIsAuthed(true);
      setUserEmail(session.user.email ?? null);
    }); 

    return () => {
      mounted = false;
      sub?.subscription?.unsubscribe();
    };
  }, [router]);

  // ✅ MINIMAL ADD: render gate prevents UI bounce/flash
  if (!authChecked) {
    return (
      <main className="min-h-screen flex items-center justify-center bg-black text-white">
        <div className="text-slate-300">Loading apps…</div>
      </main>
    );
  }
  if (!isAuthed) return null;

  // For now hardcoded (later replace with Supabase “apps registry”)
  const apps: AppCard[] = useMemo(() => ([
    {
      slug: "validation-run",
      title: "Validation Run",
      subtitle: "One-click run on real hardware with preflight + learning",
      loop_type: "validation",
      status: "Flagship",
      nudge: "Recommended",
      promise: "Get run results + gaps + exec report",
    },
    {
      slug: "digital-rtl-generator",
      title: "RTL Generator",
      subtitle: "Spec → RTL + micro-architecture summary",
      loop_type: "digital",
      status: "Flagship",
      nudge: "Most used",
      promise: "Generate clean SV + docs fast",
    },
    {
      slug: "analog-insight-explorer",
      title: "Analog Insight Explorer",
      subtitle: "Failures, sensitivity, corner risk — explained",
      loop_type: "analog",
      status: "Coming",
      nudge: "New",
      promise: "Faster debug hypotheses",
    },
    {
      slug: "firmware-bringup-assistant",
      title: "Firmware Bring-Up Assistant",
      subtitle: "Boot/UART logs → root-cause + next steps",
      loop_type: "embedded",
      status: "Coming",
      promise: "Shorten bring-up cycles",
    },
    {
      slug: "system-intelligence-analyzer",
      title: "System Intelligence Analyzer",
      subtitle: "Power/perf bottlenecks across blocks",
      loop_type: "system",
      status: "Coming",
      promise: "System-level recommendations",
    },
  ]), []);

  const featured = apps.find(a => a.slug === "validation-run") || apps[0];
  const flagship = apps.filter(a => a.status === "Flagship");
  const recommended = apps.filter(a => a.nudge === "Recommended" || a.status === "Flagship");

  const loops: LoopType[] = useMemo(() => (["validation", "digital", "analog", "embedded", "system"]), []);

  const go = (path: string) => router.push(path);

  const routeForApp = (slug: string) => {
    // Dedicated pages (apps with custom UX)
    const dedicated: Record<string, string> = {
      "validation-run": "/apps/validation-run",
      // later:
      // "digital-rtl-generator": "/apps/digital-rtl-generator",
    };
    return dedicated[slug] || `/apps/${slug}`;
  };

  return (
    <main className="min-h-screen bg-gradient-to-br from-slate-950 via-black to-slate-950 text-white">
      {/* Top bar */}
      <div className="sticky top-0 z-40 border-b border-slate-800 bg-black/70 backdrop-blur">
        <div className="mx-auto flex max-w-6xl items-center justify-between px-6 py-4">
          <button
            className="flex items-center gap-2 text-xl font-extrabold"
            onClick={() => go("/apps")}
            title="Apps Home"
          >
            <span className="text-cyan-400">CHIPLOOP</span>
            <span className="text-slate-400">/</span>
            <span className="text-slate-200">Apps</span>
          </button>

          <div className="flex items-center gap-3">
            <button
              onClick={() => go("/workflow")}
              className="rounded-xl bg-slate-800 px-4 py-2 text-slate-200 hover:bg-slate-700 transition"
              title="Advanced Builder"
            >
              Studio
            </button>
            <button
              onClick={async () => {
                await supabase.auth.signOut();
                go("/");
              }}
              className="rounded-xl border border-slate-700 px-4 py-2 text-slate-300 hover:bg-slate-900 transition"
            >
              Logout
            </button>
          </div>
        </div>
      </div>

      {/* Hero (nudges + anchors) */}
      <section className="mx-auto max-w-6xl px-6 pt-10 pb-6">
        <div className="grid gap-4 md:grid-cols-5">
          {/* Left: featured card (default choice) */}
          <div className="md:col-span-3 rounded-2xl border border-slate-800 bg-slate-900/30 p-6 shadow-lg">
            <div className="flex items-start justify-between gap-4">
              <div>
                <div className="text-xs text-slate-400">
                  Welcome{userEmail ? `, ${userEmail}` : ""} • <span className="text-cyan-300">Start here</span>
                </div>
                <h1 className="mt-2 text-3xl font-extrabold leading-tight">
                  Run outcomes, not workflows.
                </h1>
                <p className="mt-2 max-w-xl text-slate-300">
                  Pick an app, give inputs once, click run. ChipLoop handles preflight, execution, learning, and reporting.
                </p>
              </div>

              <span className="shrink-0 rounded-full border border-cyan-900/60 bg-cyan-500/10 px-3 py-1 text-xs text-cyan-200">
                Recommended
              </span>
            </div>

            <div className="mt-5 rounded-2xl border border-slate-800 bg-black/30 p-5">
              <div className="flex items-start justify-between gap-4">
                <div>
                  <div className="text-sm text-slate-400">Featured</div>
                  <div className="mt-1 text-2xl font-bold text-white">{featured.title}</div>
                  <div className="mt-1 text-slate-300">{featured.subtitle}</div>
                  {featured.promise ? (
                    <div className="mt-3 text-sm text-slate-400">
                      Outcome: <span className="text-slate-200">{featured.promise}</span>
                    </div>
                  ) : null}

                  <div className="mt-5 flex flex-wrap gap-3">
                    <button
                      onClick={() => go(`/apps/${featured.slug}`)}
                      className="rounded-xl bg-cyan-600 px-5 py-3 font-semibold hover:bg-cyan-500 transition"
                    >
                      Run now
                    </button>
                    <button
                      onClick={() => go(`/apps/${featured.slug}`)}
                      className="rounded-xl border border-slate-700 bg-slate-950/40 px-5 py-3 text-slate-200 hover:bg-slate-950 transition"
                    >
                      Preview outputs
                    </button>
                  </div>

                  {/* Micro nudge (loss aversion, reassurance) */}
                  <div className="mt-4 text-xs text-slate-500">
                    Preflight included to prevent rerun failures • Exec report generated automatically
                  </div>
                </div>

                <div className="hidden md:block w-40">
                  <div className="rounded-2xl border border-slate-800 bg-slate-950/40 p-4">
                    <div className="text-xs text-slate-400">Default path</div>
                    <div className="mt-2 space-y-2 text-sm">
                      <div className="flex items-center gap-2">
                        <span className="h-2 w-2 rounded-full bg-cyan-400" />
                        <span>Inputs</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2 w-2 rounded-full bg-cyan-400" />
                        <span>Preflight</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2 w-2 rounded-full bg-cyan-400" />
                        <span>Run</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2 w-2 rounded-full bg-cyan-400" />
                        <span>Learn</span>
                      </div>
                      <div className="flex items-center gap-2">
                        <span className="h-2 w-2 rounded-full bg-cyan-400" />
                        <span>Report</span>
                      </div>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          </div>

          {/* Right: choice controls + light nudges */}
          <div className="md:col-span-2 rounded-2xl border border-slate-800 bg-slate-900/20 p-6">
            <div className="text-sm text-slate-400">Quick choices</div>
            <div className="mt-2 text-xl font-bold">What do you want to do today?</div>

            <div className="mt-4 space-y-3">
              <button
                onClick={() => go("/apps/validation-run")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Run validation on hardware</div>
                  <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                    Recommended
                  </span>
                </div>
                <div className="mt-1 text-sm text-slate-400">Bench → instruments → preflight → run → report</div>
              </button>

              <button
                onClick={() => go("/apps/digital-rtl-generator")}
                className="w-full rounded-2xl border border-slate-800 bg-slate-950/50 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
              >
                <div className="flex items-center justify-between">
                  <div className="font-semibold">Generate RTL from spec</div>
                  <span className="rounded-full bg-slate-800 px-2 py-1 text-xs text-slate-200 border border-slate-700">
                    Most used
                  </span>
                </div>
                <div className="mt-1 text-sm text-slate-400">SV + micro-arch summary + docs</div>
              </button>

              <div className="mt-4 rounded-2xl border border-slate-800 bg-black/20 p-4">
                <div className="text-xs text-slate-400">Power move (Advanced)</div>
                <div className="mt-1 text-sm text-slate-300">
                  Build your own apps in <span className="text-cyan-300">Studio</span> and publish into Apps.
                </div>
                <button
                  onClick={() => go("/workflow")}
                  className="mt-3 w-full rounded-xl bg-slate-800 px-4 py-2 hover:bg-slate-700"
                >
                  Open Studio
                </button>
              </div>
            </div>

            {/* View toggle (choice architecture: default recommended) */}
            <div className="mt-6 flex items-center gap-2">
              <button
                onClick={() => setView("recommended")}
                className={`rounded-xl px-4 py-2 text-sm border transition ${
                  view === "recommended"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                }`}
              >
                Recommended
              </button>
              <button
                onClick={() => setView("all")}
                className={`rounded-xl px-4 py-2 text-sm border transition ${
                  view === "all"
                    ? "border-cyan-700 bg-cyan-500/10 text-cyan-200"
                    : "border-slate-800 bg-slate-950/20 text-slate-300 hover:bg-slate-950/40"
                }`}
              >
                Explore all loops
              </button>
            </div>
          </div>
        </div>
      </section>

      {/* Flagship row (anchoring + easy first decision) */}
      <section className="mx-auto max-w-6xl px-6 pb-4">
        <div className="mb-3 flex items-end justify-between">
          <div>
            <div className="text-lg font-bold">Flagship apps</div>
            <div className="text-sm text-slate-400">Best starting points to feel the ChipLoop philosophy.</div>
          </div>
        </div>

        <div className="grid gap-4 md:grid-cols-2">
          {flagship.map((app) => (
            <button
              key={app.slug}
              onClick={() => go(routeForApp(app.slug))}
              className="rounded-2xl border border-slate-800 bg-slate-950/50 p-5 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
            >
              <div className="flex items-center justify-between gap-3">
                <div className="text-xl font-bold">{app.title}</div>
                <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                  {app.nudge || "Flagship"}
                </span>
              </div>
              <div className="mt-2 text-slate-300">{app.subtitle}</div>
              {app.promise ? <div className="mt-3 text-sm text-slate-400">Outcome: <span className="text-slate-200">{app.promise}</span></div> : null}
              <div className="mt-4 text-xs text-slate-500">One click → progressive outputs → executive summary</div>
            </button>
          ))}
        </div>
      </section>

      {/* Loop rows (Netflix/YouTube style) */}
      <section className="mx-auto max-w-6xl px-6 pb-16 space-y-10">
        {(view === "recommended" ? loops.filter(l => l === "validation" || l === "digital") : loops).map((loop) => {
          const meta = LOOP_META[loop];
          const rowApps = apps.filter((a) => a.loop_type === loop);

          // Duplicate to create “infinite feel”
          const animatedApps = [...rowApps, ...rowApps, ...rowApps];

          return (
            <div key={loop}>
              <div className="mb-3 flex items-end justify-between">
                <div>
                  <div className="flex items-center gap-2">
                    <div className={`h-2 w-2 rounded-full ${meta.accent}`} />
                    <div className="text-xl font-bold">{meta.title}</div>
                  </div>
                  <div className="text-sm text-slate-400">{meta.tagline}</div>
                </div>

                <button
                  onClick={() => setView("all")}
                  className="text-sm text-cyan-300 hover:underline"
                >
                  See all
                </button>
              </div>

              <div className="relative overflow-hidden rounded-2xl border border-slate-800 bg-slate-900/15">
                <div className="pointer-events-none absolute inset-y-0 left-0 w-16 bg-gradient-to-r from-black to-transparent" />
                <div className="pointer-events-none absolute inset-y-0 right-0 w-16 bg-gradient-to-l from-black to-transparent" />

                <div className="marquee flex gap-4 py-5 px-4">
                  {animatedApps.map((app, idx) => (
                    <button
                      key={`${app.slug}-${idx}`}
                      onClick={() => go(routeForApp(app.slug))}
                      className="min-w-[280px] max-w-[280px] rounded-2xl border border-slate-800 bg-slate-950/55 p-4 text-left hover:border-cyan-700 hover:bg-slate-950 transition"
                    >
                      <div className="flex items-center justify-between gap-2">
                        <div className="text-lg font-bold text-slate-100">{app.title}</div>
                        {app.status ? (
                          <span className="rounded-full border border-slate-700 bg-slate-900/40 px-2 py-1 text-xs text-slate-200">
                            {app.status}
                          </span>
                        ) : null}
                      </div>

                      <div className="mt-2 text-sm text-slate-300">{app.subtitle}</div>

                      <div className="mt-3 flex items-center justify-between">
                        {app.nudge ? (
                          <span className="rounded-full bg-cyan-500/10 px-2 py-1 text-xs text-cyan-200 border border-cyan-900/60">
                            {app.nudge}
                          </span>
                        ) : <span />}

                        <span className="text-xs text-slate-500">Open →</span>
                      </div>
                    </button>
                  ))}
                </div>
              </div>
            </div>
          );
        })}
      </section>

      <style jsx>{`
        .marquee {
          width: max-content;
          animation: marquee 22s linear infinite;
        }
        @keyframes marquee {
          0% { transform: translateX(0); }
          100% { transform: translateX(-33.333%); }
        }
        .accent-digital { background: #22c55e; }
        .accent-validation { background: #06b6d4; }
        .accent-analog { background: #a855f7; }
        .accent-embedded { background: #f97316; }
        .accent-system { background: #eab308; }

        /* Respect reduced motion */
        @media (prefers-reduced-motion: reduce) {
          .marquee { animation: none; }
        }
      `}</style>
    </main>
  );
}