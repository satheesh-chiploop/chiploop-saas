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
  interest_area: "General question",
  preferred_time: "",
  message: "",
};

const interestOptions = [
  "General question",
  "Starter / Pro / Pro Max pricing",
  "Digital Design Loop",
  "Digital Implementation Loop",
  "Mixed Signal Loop",
  "Firmware/Software Loop",
  "Validation Loop",
  "Products and reference journeys",
  "SDK / CLI / private deployment",
  "Investor or partnership discussion",
];

export default function ContactPage() {
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
        body: JSON.stringify({ ...form, source: "contact_page" }),
      });
      const data = await response.json().catch(() => ({}));
      if (!response.ok) {
        const detail = typeof data?.detail === "string" ? data.detail : "Contact request failed";
        throw new Error(detail);
      }
      setSuccess(true);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Contact request failed");
    } finally {
      setLoading(false);
    }
  };

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="contact" showMarketplace showSettings={false} />
      <div className="w-full border-b border-slate-800 bg-[radial-gradient(circle_at_50%_0%,rgba(34,211,238,0.14),transparent_34%),linear-gradient(180deg,#020617_0%,#0f172a_58%,#020617_100%)] px-6 py-10">
        <div className="mx-auto max-w-[1200px]">
        <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr]">
          <section className="rounded-lg border border-slate-800 bg-slate-900/70 p-8">
            <p className="text-xs font-semibold uppercase text-cyan-300">Contact Us</p>
            <h1 className="mt-4 text-5xl font-extrabold leading-[1.05] text-white sm:text-6xl">Tell us what you want to discuss.</h1>
            <p className="mt-5 leading-7 text-slate-300">
              Send a question, partnership note, pricing question, or product request. The ChipLoop team receives a copy.
            </p>
            <div className="mt-8 rounded-lg border border-slate-700 bg-slate-950/70 p-5 text-sm text-slate-300">
              <div className="font-bold text-white">Email</div>
              <a href="mailto:chiploop.agx@gmail.com" className="mt-2 block text-slate-100 hover:text-cyan-200">
                chiploop.agx@gmail.com
              </a>
            </div>
          </section>

          <section className="rounded-lg border border-slate-800 bg-white p-8 text-slate-950 shadow-2xl">
            {success ? (
              <div className="flex min-h-[480px] flex-col justify-center">
                <div className="w-fit rounded-full bg-emerald-100 px-4 py-2 text-sm font-bold text-emerald-800">Request received</div>
                <h2 className="mt-6 text-4xl font-extrabold leading-tight text-slate-950 sm:text-5xl">Thanks, we received your note.</h2>
                <p className="mt-4 leading-7 text-slate-600">
                  We recorded your details and will use your email to follow up.
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
                  <h2 className="text-3xl font-extrabold leading-tight text-slate-950 sm:text-4xl">Contact ChipLoop</h2>
                  <p className="mt-2 text-sm text-slate-600">A few details help us route the request.</p>
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
                    <span className="text-sm font-semibold text-slate-700">Topic</span>
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
                    <span className="text-sm font-semibold text-slate-700">Preferred time</span>
                    <input
                      value={form.preferred_time}
                      onChange={(event) => update("preferred_time", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Optional"
                    />
                  </label>
                </div>

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">Message</span>
                  <textarea
                    value={form.message}
                    onChange={(event) => update("message", event.target.value)}
                    className="mt-2 min-h-28 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    placeholder="Tell us how we can help."
                  />
                </label>

                {error ? <div className="rounded-lg bg-red-50 px-4 py-3 text-sm font-semibold text-red-700">{error}</div> : null}

                <button
                  type="submit"
                  disabled={loading}
                  className="w-full rounded-lg bg-slate-950 px-5 py-3 font-bold text-white transition hover:bg-slate-800 disabled:cursor-not-allowed disabled:opacity-60"
                >
                  {loading ? "Submitting..." : "Submit Contact Request"}
                </button>
              </form>
            )}
          </section>
        </div>
        </div>
      </div>
    </main>
  );
}
