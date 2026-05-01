"use client";

import { FormEvent, useState } from "react";
import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";

type FormState = {
  name: string;
  email: string;
  company: string;
  role: string;
  loop_interest: string;
  preferred_session: string;
  questions: string;
};

const initialForm: FormState = {
  name: "",
  email: "",
  company: "",
  role: "",
  loop_interest: "Digital",
  preferred_session: "9am_pst",
  questions: "",
};

const loopOptions = ["Digital", "Embedded", "Software", "Validation", "Analog", "Physical Design", "System", "Still exploring"];

export default function WebinarRegistrationPage() {
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
      const response = await fetch("/api/webinar/register", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ ...form, source: "landing_page" }),
      });
      const data = await response.json().catch(() => ({}));
      if (!response.ok) {
        throw new Error(typeof data?.detail === "string" ? data.detail : "Registration failed");
      }
      setSuccess(true);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Registration failed");
    } finally {
      setLoading(false);
    }
  };

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="webinar" showWebinar showSettings={false} maxWidthClass="max-w-5xl" />
      <div className="mx-auto max-w-5xl px-6 py-10">
        <div className="grid grid-cols-1 gap-8 lg:grid-cols-[0.9fr_1.1fr]">
          <section className="rounded-2xl border border-slate-800 bg-slate-900/70 p-8">
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Weekly ChipLoop Webinar</p>
            <h1 className="mt-4 text-4xl font-extrabold leading-tight">Register for the Saturday ChipLoop demo</h1>
            <p className="mt-5 leading-7 text-slate-300">
              Join a 30-minute walkthrough every Saturday starting May 23, 2026. Choose 9:00 AM PST or 9:00 PM PST.
            </p>
            <div className="mt-8 rounded-xl border border-slate-700 bg-slate-950/70 p-5 text-sm text-slate-300">
              <div className="font-bold text-white">We will cover:</div>
              <ul className="mt-3 space-y-2">
                <li>What ChipLoop is and how Loops work</li>
                <li>Apps vs Studio</li>
                <li>Connected design data across domains</li>
                <li>Guided Arch2RTL demo</li>
                <li>Generated RTL, SDC, UPF, and downloadable artifacts</li>
                <li>Q&A</li>
              </ul>
            </div>
          </section>

          <section className="rounded-2xl border border-slate-800 bg-white p-8 text-slate-950 shadow-2xl">
            {success ? (
              <div className="flex min-h-[420px] flex-col justify-center">
                <div className="rounded-full bg-emerald-100 px-4 py-2 text-sm font-bold text-emerald-800 w-fit">Registration received</div>
                <h2 className="mt-6 text-3xl font-extrabold">You are registered.</h2>
                <p className="mt-4 leading-7 text-slate-600">
                  Thanks for registering. We captured your preferred session and will use your email for webinar updates.
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
                  <h2 className="text-2xl font-extrabold">Save your seat</h2>
                  <p className="mt-2 text-sm text-slate-600">A few details help us tailor the demo to your interests.</p>
                </div>

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

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Company / School</span>
                    <input
                      value={form.company}
                      onChange={(event) => update("company", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Optional"
                    />
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Role</span>
                    <input
                      value={form.role}
                      onChange={(event) => update("role", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                      placeholder="Student, engineer, founder..."
                    />
                  </label>
                </div>

                <div className="grid grid-cols-1 gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Loop interest</span>
                    <select
                      value={form.loop_interest}
                      onChange={(event) => update("loop_interest", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    >
                      {loopOptions.map((loop) => (
                        <option key={loop} value={loop}>{loop}</option>
                      ))}
                    </select>
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Preferred session</span>
                    <select
                      required
                      value={form.preferred_session}
                      onChange={(event) => update("preferred_session", event.target.value)}
                      className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    >
                      <option value="9am_pst">Saturday 9:00 AM PST</option>
                      <option value="9pm_pst">Saturday 9:00 PM PST</option>
                      <option value="either">Either session works</option>
                    </select>
                  </label>
                </div>

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">Questions or topics</span>
                  <textarea
                    value={form.questions}
                    onChange={(event) => update("questions", event.target.value)}
                    className="mt-2 min-h-28 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500"
                    placeholder="Optional: tell us what you want to see"
                  />
                </label>

                {error && <div className="rounded-lg bg-red-50 px-4 py-3 text-sm font-semibold text-red-700">{error}</div>}

                <button
                  disabled={loading}
                  className="w-full rounded-lg bg-cyan-500 px-5 py-3 font-bold text-slate-950 transition hover:bg-cyan-400 disabled:cursor-not-allowed disabled:bg-slate-300"
                >
                  {loading ? "Registering..." : "Register for Webinar"}
                </button>
              </form>
            )}
          </section>
        </div>
      </div>
    </main>
  );
}
