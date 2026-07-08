"use client";

import { FormEvent, useState } from "react";
import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

type FormState = {
  name: string;
  email: string;
  phone: string;
  organization_type: "Individual" | "Company" | "University";
  organization_name: string;
  role: string;
  interest_area: string;
  preferred_time: string;
  message: string;
};

const initialForm: FormState = {
  name: "",
  email: "",
  phone: "",
  organization_type: "Company",
  organization_name: "",
  role: "",
  interest_area: "End-to-end chip journey",
  preferred_time: "",
  message: "",
};

const interestOptions = [
  "End-to-end chip journey",
  "RTL design",
  "Verification",
  "Firmware and software",
  "Software-hardware co-simulation",
  "Tapeout / physical design",
  "Product demo / reference journey",
  "Custom workflows and private agents",
  "SDK / CLI / private deployment",
];

export default function BookDemoPage() {
  const router = useRouter();
  const [form, setForm] = useState<FormState>(initialForm);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [success, setSuccess] = useState(false);

  const update = (field: keyof FormState, value: string) => {
    setForm((current) => ({ ...current, [field]: value }));
  };

  const submit = async (event: FormEvent<HTMLFormElement>) => {
    event.preventDefault();
    setLoading(true);
    setError(null);

    try {
      const response = await fetch("/api/demo-requests", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ ...form, source: "book_demo_page" }),
      });
      const data = await response.json().catch(() => ({}));
      if (!response.ok) {
        const detail = typeof data?.detail === "string" ? data.detail : "Demo request failed";
        throw new Error(detail);
      }
      setSuccess(true);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Demo request failed");
    } finally {
      setLoading(false);
    }
  };

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="demo" showMarketplace showSettings={false} />
      <div className="mx-auto max-w-[1440px] px-6 py-10">
        <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.85fr_1.15fr]">
          <section className="rounded-2xl border border-slate-800 bg-slate-900/70 p-8">
            <p className="text-xs font-semibold uppercase text-cyan-300">Book Demo</p>
            <h1 className="mt-4 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">See how ChipLoop connects the chip design journey.</h1>
            <p className="mt-5 leading-7 text-slate-300">
              Tell us about your team and what you want to build. We will follow up with a focused ChipLoop demo.
            </p>
            <div className="mt-8 rounded-xl border border-slate-700 bg-slate-950/70 p-5 text-sm text-slate-300">
              <div className="font-bold text-white">A demo can cover:</div>
              <ul className="mt-3 space-y-2">
                <li>- Requirements to RTL, verification, firmware, software, and validation</li>
                <li>- Prebuilt apps, custom workflows, private agents, and products</li>
                <li>- Agent execution logs, artifacts, dashboards, and handoffs</li>
                <li>- SDK, CLI, and private environment integration</li>
              </ul>
            </div>
            <div className="mt-5 rounded-xl border border-cyan-800 bg-cyan-950/25 p-5 text-sm text-cyan-100">
              <div className="font-bold text-white">Looking for a quick start?</div>
              <p className="mt-2 leading-6 text-cyan-100/85">
                You can also explore the guided Arch2RTL demo while we review your request.
              </p>
              <button
                type="button"
                onClick={() => router.push("/apps/arch2rtl?guided=1")}
                className="mt-4 rounded-lg bg-cyan-400 px-4 py-2 font-bold text-slate-950 transition hover:bg-cyan-300"
              >
                Start Arch2RTL Demo
              </button>
            </div>
          </section>

          <section className="rounded-2xl border border-slate-800 bg-white p-8 text-slate-950 shadow-2xl">
            {success ? (
              <div className="flex min-h-[520px] flex-col justify-center">
                <div className="w-fit rounded-full bg-emerald-100 px-4 py-2 text-sm font-bold text-emerald-800">Request received</div>
                <h2 className="mt-6 text-4xl font-extrabold leading-tight text-white sm:text-5xl">Thanks, we received your demo request.</h2>
                <p className="mt-4 leading-7 text-slate-600">
                  A copy was recorded for the ChipLoop team. We will use your email to follow up with next steps.
                </p>
                <button
                  onClick={() => router.push("/")}
                  className="mt-8 rounded-lg bg-slate-950 px-5 py-3 font-bold text-white hover:bg-slate-800"
                >
                  Back to landing page
                </button>
              </div>
            ) : (
              <form onSubmit={submit} className="space-y-5">
                <div>
                  <h2 className="text-3xl font-extrabold leading-tight text-white sm:text-4xl">Request a demo</h2>
                  <p className="mt-2 text-sm text-slate-600">A few details help us tailor the discussion.</p>
                </div>

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Name</span>
                    <input
                      required
                      value={form.name}
                      onChange={(event) => update("name", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Your name"
                    />
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Email</span>
                    <input
                      required
                      type="email"
                      value={form.email}
                      onChange={(event) => update("email", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="you@example.com"
                    />
                  </label>
                </div>

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Phone number</span>
                    <input
                      value={form.phone}
                      onChange={(event) => update("phone", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Optional"
                    />
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Organization type</span>
                    <select
                      required
                      value={form.organization_type}
                      onChange={(event) => update("organization_type", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    >
                      <option value="Individual">Individual</option>
                      <option value="Company">Company</option>
                      <option value="University">University</option>
                    </select>
                  </label>
                </div>

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Organization name</span>
                    <input
                      value={form.organization_name}
                      onChange={(event) => update("organization_name", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Company, university, or lab"
                    />
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Role / title</span>
                    <input
                      value={form.role}
                      onChange={(event) => update("role", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Founder, engineer, professor..."
                    />
                  </label>
                </div>

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Interest area</span>
                    <select
                      value={form.interest_area}
                      onChange={(event) => update("interest_area", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    >
                      {interestOptions.map((interest) => (
                        <option key={interest} value={interest}>{interest}</option>
                      ))}
                    </select>
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Preferred meeting time</span>
                    <input
                      value={form.preferred_time}
                      onChange={(event) => update("preferred_time", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Example: Tue morning PT"
                    />
                  </label>
                </div>

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">What would you like to discuss?</span>
                  <textarea
                    value={form.message}
                    onChange={(event) => update("message", event.target.value)}
                    className="mt-2 min-h-28 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    placeholder="Tell us about your chip design flow, team, or demo interest."
                  />
                </label>

                {error ? <div className="rounded-lg bg-red-50 px-4 py-3 text-sm font-semibold text-red-700">{error}</div> : null}

                <button
                  type="submit"
                  disabled={loading}
                  className="w-full rounded-lg bg-slate-950 px-5 py-3 font-bold text-white transition hover:bg-slate-800 disabled:cursor-not-allowed disabled:opacity-60"
                >
                  {loading ? "Submitting..." : "Submit Demo Request"}
                </button>
              </form>
            )}
          </section>
        </div>
      </div>
    </main>
  );
}
