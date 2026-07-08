"use client";

import { useEffect, useState } from "react";
import { usePathname, useRouter } from "next/navigation";
import { createClientComponentClient } from "@/lib/platformClient";
import type { User } from "@supabase/supabase-js";
import { PlanCreditBadge } from "@/components/PlanCreditStatus";

type NavKey = "home" | "loops" | "apps" | "products" | "studio" | "marketplace" | "pricing" | "events" | "help" | "settings" | "admin" | "webinar" | "workshop" | "demo" | "contact";

type TopNavProps = {
  current?: NavKey;
  showPlanBadge?: boolean;
  showMarketplace?: boolean;
  showWebinar?: boolean;
  showWorkshop?: boolean;
  showSettings?: boolean;
  showAdmin?: boolean;
  maxWidthClass?: string;
  className?: string;
};

const navButtonClass = "whitespace-nowrap text-[15px] font-medium text-slate-300 transition hover:text-cyan-300";
const activeNavButtonClass = "whitespace-nowrap text-[15px] font-semibold text-cyan-200 transition hover:text-cyan-100";


function AnimatedTesseractLogo() {
  return (
    <span
      className="relative flex h-12 w-12 shrink-0 items-center justify-center rounded-lg border border-cyan-300/70 bg-cyan-400/10 shadow-[0_0_24px_rgba(34,211,238,0.3)] transition group-hover:border-cyan-100 group-hover:bg-cyan-300/15"
      aria-hidden="true"
    >
      <svg className="h-9 w-9 text-cyan-200" viewBox="0 0 64 64" fill="none">
        <g stroke="currentColor" strokeWidth="2.4" strokeLinecap="round" strokeLinejoin="round">
          <g opacity="0.95">
            <path d="M14 18h28v28H14z" />
            <path d="M22 10h28v28H22z" />
            <path d="M14 18 22 10" />
            <path d="M42 18 50 10" />
            <path d="M42 46 50 38" />
            <path d="M14 46 22 38" />
            <animateTransform
              attributeName="transform"
              type="rotate"
              from="0 32 32"
              to="360 32 32"
              dur="9s"
              repeatCount="indefinite"
            />
          </g>
          <g opacity="0.55">
            <path d="M20 24h20v20H20z" />
            <path d="M25 19h20v20H25z" />
            <path d="M20 24 25 19" />
            <path d="M40 24 45 19" />
            <path d="M40 44 45 39" />
            <path d="M20 44 25 39" />
            <animateTransform
              attributeName="transform"
              type="rotate"
              from="360 32 32"
              to="0 32 32"
              dur="6s"
              repeatCount="indefinite"
            />
          </g>
        </g>
        <circle cx="32" cy="32" r="2.8" className="fill-cyan-200">
          <animate attributeName="opacity" values="0.55;1;0.55" dur="2.4s" repeatCount="indefinite" />
        </circle>
      </svg>
    </span>
  );
}


function getDisplayName(user: User | null): string | null {
  if (!user) return null;
  const metadata = user.user_metadata || {};
  const rawName =
    typeof metadata.full_name === "string" ? metadata.full_name :
    typeof metadata.name === "string" ? metadata.name :
    typeof metadata.first_name === "string" ? metadata.first_name :
    user.email || "";
  const trimmed = rawName.trim();
  if (!trimmed) return null;
  return trimmed.includes("@") ? trimmed.split("@")[0] : trimmed.split(/\s+/)[0];
}

export default function TopNav({
  current,
  showPlanBadge = false,
  showMarketplace = false,
  showWebinar = false,
  showWorkshop = false,
  showSettings = true,
  showAdmin = false,
  maxWidthClass = "max-w-7xl",
  className = "sticky top-0 z-50",
}: TopNavProps) {
  const router = useRouter();
  const pathname = usePathname();
  const supabase = createClientComponentClient();
  const [displayName, setDisplayName] = useState<string | null>(null);
  const [authChecked, setAuthChecked] = useState(false);

  useEffect(() => {
    let mounted = true;

    async function loadSession() {
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (mounted) {
        setDisplayName(getDisplayName(session?.user || null));
        setAuthChecked(true);
      }
    }

    const {
      data: { subscription },
    } = supabase.auth.onAuthStateChange((_event, session) => {
      if (!mounted) return;
      setDisplayName(getDisplayName(session?.user || null));
      setAuthChecked(true);
    });

    loadSession();
    return () => {
      mounted = false;
      subscription.unsubscribe();
    };
  }, [supabase]);

  const links: Array<{ key: NavKey; label: string; href: string; show: boolean }> = [
    { key: "home", label: "Home", href: "/", show: true },
    { key: "loops", label: "Loops", href: "/loops", show: true },
    { key: "apps", label: "Apps", href: "/apps", show: true },
    { key: "products", label: "Products", href: "/products", show: true },
    { key: "studio", label: "Studio", href: "/workflow", show: true },
    { key: "marketplace", label: "Marketplace", href: "/marketplace", show: showMarketplace },
    { key: "pricing", label: "Pricing", href: "/pricing", show: true },
    { key: "demo", label: "Book Demo", href: "/book-demo", show: true },
    { key: "events", label: "Events", href: "/events", show: showWebinar || showWorkshop },
    { key: "help", label: "Playbook", href: "/help", show: false },
    { key: "settings", label: "Settings", href: "/settings/plan", show: showSettings },
    { key: "admin", label: "Admin", href: "/admin/marketplace", show: showAdmin },
    { key: "webinar", label: "Webinar", href: "/webinar/register", show: showWebinar },
    { key: "workshop", label: "Workshop", href: "/workshop", show: showWorkshop },
  ];

  const next = current === "home" ? "/apps" : pathname || "/apps";

  return (
    <nav className={`${className} border-b border-slate-800 bg-slate-950/90 backdrop-blur`}>
      <div className={`mx-auto flex min-w-0 ${maxWidthClass} flex-col gap-3 px-4 py-3 sm:flex-row sm:items-center sm:justify-between sm:px-6 sm:py-4`}>
        <button
          onClick={() => router.push("/")}
          className="group flex shrink-0 self-start items-center gap-3 text-2xl font-extrabold text-cyan-300 sm:self-auto"
          aria-label="ChipLoop home"
        >
          <AnimatedTesseractLogo />
          <span>ChipLoop</span>
        </button>

        <div className="flex min-w-0 flex-1 items-center gap-4 overflow-x-auto pb-1 sm:w-auto sm:flex-nowrap sm:justify-end sm:gap-4 sm:pb-0 xl:gap-5">
          {showPlanBadge ? <PlanCreditBadge /> : null}
          {links.filter((link) => link.show).map((link) => (
            <button
              key={link.key}
              onClick={() => router.push(link.href)}
              className={
                link.key === "demo"
                  ? "whitespace-nowrap rounded-lg bg-cyan-400 px-3 py-2 text-[15px] font-bold text-slate-950 transition hover:bg-cyan-300 sm:px-4"
                  : current === link.key
                  ? activeNavButtonClass
                  : navButtonClass
              }
            >
              {link.label}
            </button>
          ))}
          {authChecked ? displayName ? (
            <button
              onClick={async () => {
                await supabase.auth.signOut();
                setDisplayName(null);
                router.push("/login");
              }}
              className="whitespace-nowrap rounded-lg border border-slate-700 px-3 py-2 text-[15px] font-semibold text-slate-300 transition hover:bg-slate-900 hover:text-cyan-200 sm:px-4"
            >
              <span className="mr-2 text-cyan-200">Hi, {displayName}</span>Logout
            </button>
          ) : (
            <button
              onClick={() => router.push(`/login?next=${encodeURIComponent(next)}`)}
              className="whitespace-nowrap text-[15px] font-medium text-slate-300 transition hover:text-cyan-300"
            >
              Login
            </button>
          ) : null}
        </div>
      </div>
    </nav>
  );
}

