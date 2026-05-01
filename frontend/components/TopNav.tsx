"use client";

import { useEffect, useState } from "react";
import { usePathname, useRouter } from "next/navigation";
import { createClient } from "@supabase/supabase-js";
import { PlanCreditBadge } from "@/components/PlanCreditStatus";

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL!;
const supabaseAnonKey = process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!;
const supabase = createClient(supabaseUrl, supabaseAnonKey);

type NavKey = "home" | "apps" | "studio" | "marketplace" | "pricing" | "settings" | "admin" | "webinar";

type TopNavProps = {
  current?: NavKey;
  showPlanBadge?: boolean;
  showMarketplace?: boolean;
  showWebinar?: boolean;
  showSettings?: boolean;
  showAdmin?: boolean;
  maxWidthClass?: string;
  className?: string;
};

const navButtonClass = "text-sm font-medium text-slate-300 transition hover:text-cyan-300";
const activeNavButtonClass = "text-sm font-semibold text-cyan-200 transition hover:text-cyan-100";

export default function TopNav({
  current,
  showPlanBadge = false,
  showMarketplace = false,
  showWebinar = false,
  showSettings = true,
  showAdmin = false,
  maxWidthClass = "max-w-7xl",
  className = "sticky top-0 z-50",
}: TopNavProps) {
  const router = useRouter();
  const pathname = usePathname();
  const [userEmail, setUserEmail] = useState<string | null>(null);
  const [authChecked, setAuthChecked] = useState(false);

  useEffect(() => {
    let mounted = true;
    async function loadSession() {
      const {
        data: { session },
      } = await supabase.auth.getSession();
      if (mounted) {
        setUserEmail(session?.user?.email || null);
        setAuthChecked(true);
      }
    }
    loadSession();
    return () => {
      mounted = false;
    };
  }, []);

  const links: Array<{ key: NavKey; label: string; href: string; show: boolean }> = [
    { key: "home", label: "Home", href: "/", show: true },
    { key: "apps", label: "Apps", href: "/apps", show: true },
    { key: "studio", label: "Studio", href: "/workflow", show: true },
    { key: "marketplace", label: "Marketplace", href: "/marketplace", show: showMarketplace },
    { key: "pricing", label: "Pricing", href: "/pricing", show: true },
    { key: "settings", label: "Settings", href: "/settings/plan", show: showSettings },
    { key: "admin", label: "Admin", href: "/admin/marketplace", show: showAdmin },
    { key: "webinar", label: "Webinar", href: "/webinar/register", show: showWebinar },
  ];

  const next = current === "home" ? "/apps" : pathname || "/apps";

  return (
    <nav className={`${className} border-b border-slate-800 bg-slate-950/90 backdrop-blur`}>
      <div className={`mx-auto flex ${maxWidthClass} items-center justify-between px-6 py-4`}>
        <button
          onClick={() => router.push("/")}
          className="text-xl font-extrabold text-cyan-300"
          aria-label="ChipLoop home"
        >
          ChipLoop
        </button>

        <div className="flex flex-wrap items-center justify-end gap-5">
          {showPlanBadge ? <PlanCreditBadge /> : null}
          {links.filter((link) => link.show).map((link) => (
            <button
              key={link.key}
              onClick={() => router.push(link.href)}
              className={current === link.key ? activeNavButtonClass : navButtonClass}
            >
              {link.label}
            </button>
          ))}
          {authChecked ? userEmail ? (
            <button
              onClick={async () => {
                await supabase.auth.signOut();
                setUserEmail(null);
                router.push("/");
              }}
              className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-300 transition hover:bg-slate-900 hover:text-cyan-200"
            >
              Logout
            </button>
          ) : (
            <button
              onClick={() => router.push(`/login?next=${encodeURIComponent(next)}`)}
              className="text-sm font-medium text-slate-300 transition hover:text-cyan-300"
            >
              Login
            </button>
          ) : null}
        </div>
      </div>
    </nav>
  );
}

