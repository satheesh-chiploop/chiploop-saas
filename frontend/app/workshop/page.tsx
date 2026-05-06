"use client";

import { FormEvent, Suspense, useEffect, useMemo, useState } from "react";
import { useRouter, useSearchParams } from "next/navigation";
import TopNav from "@/components/TopNav";

type FormState = {
  name: string;
  email: string;
  company: string;
  role: string;
  loop_interest: string;
  batch_id: string;
  questions: string;
};

type WorkshopBatch = {
  id: string;
  label: string;
  day_1: string;
  day_2: string;
  time: string;
  timezone: string;
  capacity: number;
  booked: number;
  remaining: number;
  full: boolean;
  price_usd: number;
};

type RegistrationStatus = {
  id: string;
  email: string;
  batch_id: string;
  payment_status: string;
  paid: boolean;
};

const initialForm: FormState = {
  name: "",
  email: "",
  company: "",
  role: "",
  loop_interest: "Digital",
  batch_id: "",
  questions: "",
};

const dayOne = [
  "Welcome to Agentic AI in chip design",
  "Why prompt-based AI falls short",
  "From prompts to structured workflows",
  "Understanding agents and engineering artifacts",
  "Introduction to ChipLoop and system thinking",
  "First end-to-end workflow walkthrough",
  "Key takeaways and reflection",
];

const dayTwo = [
  "Recap: from prompts to systems",
  "Designing a Digital RTL Agent",
  "Defining inputs, outputs, and execution flow",
  "Building reliable prompt architecture",
  "From agent to workflow integration",
  "Connecting RTL, simulation, and firmware concepts",
  "System thinking for real-world chip design",
  "Next steps: building and scaling your own workflows",
];

const loopOptions = ["Digital", "Embedded", "Software", "Validation", "Analog", "Physical Design", "System", "Still exploring"];

function batchOptionLabel(batch: WorkshopBatch): string {
  if (batch.full) return `${batch.label} - Full`;
  if (batch.remaining > 0 && batch.remaining <= 4) {
    return `${batch.label} - ${batch.remaining} seat${batch.remaining === 1 ? "" : "s"} left`;
  }
  return batch.label;
}

function WorkshopContent() {
  const router = useRouter();
  const searchParams = useSearchParams();
  const [form, setForm] = useState<FormState>(initialForm);
  const [batches, setBatches] = useState<WorkshopBatch[]>([]);
  const [batchesLoading, setBatchesLoading] = useState(true);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [registration, setRegistration] = useState<RegistrationStatus | null>(null);

  const selectedBatch = useMemo(
    () => batches.find((batch) => batch.id === form.batch_id),
    [batches, form.batch_id]
  );

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const response = await fetch("/api/workshop/batches", { cache: "no-store" });
        const data = await response.json().catch(() => ({}));
        if (!response.ok) throw new Error("Unable to load workshop batches");
        const loaded = Array.isArray(data?.batches) ? data.batches as WorkshopBatch[] : [];
        if (!mounted) return;
        setBatches(loaded);
        const firstOpen = loaded.find((batch) => !batch.full);
        if (firstOpen) {
          setForm((current) => current.batch_id ? current : { ...current, batch_id: firstOpen.id });
        }
      } catch (err) {
        if (mounted) setError(err instanceof Error ? err.message : "Unable to load workshop batches");
      } finally {
        if (mounted) setBatchesLoading(false);
      }
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    const registrationId = searchParams.get("registration_id");
    if (!registrationId) return;
    let mounted = true;
    (async () => {
      try {
        const response = await fetch(`/api/workshop/registrations/${registrationId}`, { cache: "no-store" });
        const data = await response.json().catch(() => ({}));
        if (!response.ok) return;
        if (mounted) setRegistration(data.registration || null);
      } catch {
        if (mounted) setRegistration(null);
      }
    })();
    return () => { mounted = false; };
  }, [searchParams]);

  function update(field: keyof FormState, value: string) {
    setForm((current) => ({ ...current, [field]: value }));
  }

  async function submit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setLoading(true);
    setError(null);
    try {
      const response = await fetch("/api/workshop/checkout", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ ...form, source: "workshop_page" }),
      });
      const data = await response.json().catch(() => ({}));
      if (!response.ok) {
        const detail = typeof data?.detail === "string" ? data.detail : "Workshop checkout failed";
        throw new Error(detail === "batch_full" ? "That batch just filled up. Please choose another slot." : detail);
      }
      if (!data.url) throw new Error("Stripe checkout URL was not returned.");
      window.location.href = data.url;
    } catch (err) {
      setError(err instanceof Error ? err.message : "Workshop checkout failed");
    } finally {
      setLoading(false);
    }
  }

  const payment = searchParams.get("payment");

  return (
    <main className="min-h-screen bg-slate-950 text-white">
      <TopNav current="workshop" showWebinar showWorkshop showSettings={false} maxWidthClass="max-w-6xl" />
      <div className="mx-auto max-w-6xl px-6 py-10">
        <div className="grid gap-8 lg:grid-cols-[1fr_0.9fr]">
          <section className="rounded-2xl border border-slate-800 bg-slate-900/70 p-8">
            <p className="text-sm font-bold uppercase tracking-wide text-cyan-300">Paid Workshop</p>
            <h1 className="mt-4 text-4xl font-extrabold leading-tight">Agentic AI in Chip Design</h1>
            <p className="mt-5 leading-7 text-slate-300">
              A hands-on 2-day workshop across two consecutive Saturdays. Each session runs for 2 hours.
              Choose the 9:30 AM PST or 9:30 PM PST batch. New cohorts open every other Saturday.
            </p>
            <div className="mt-6 flex flex-wrap gap-3">
              <span className="rounded-full border border-cyan-700 bg-cyan-950/40 px-4 py-2 text-sm font-semibold text-cyan-100">$99 per workshop</span>
              <span className="rounded-full border border-slate-700 bg-slate-950 px-4 py-2 text-sm font-semibold text-slate-200">2 Saturdays</span>
              <span className="rounded-full border border-slate-700 bg-slate-950 px-4 py-2 text-sm font-semibold text-slate-200">2 hours each day</span>
            </div>

            <div className="mt-8 grid gap-5 md:grid-cols-2">
              <div className="rounded-xl border border-slate-800 bg-slate-950/70 p-5">
                <h2 className="text-lg font-bold text-cyan-200">Day 1: Foundations to First System</h2>
                <ul className="mt-4 space-y-2 text-sm leading-6 text-slate-300">
                  {dayOne.map((item) => <li key={item}>- {item}</li>)}
                </ul>
              </div>
              <div className="rounded-xl border border-slate-800 bg-slate-950/70 p-5">
                <h2 className="text-lg font-bold text-cyan-200">Day 2: Build, Connect, and Scale</h2>
                <ul className="mt-4 space-y-2 text-sm leading-6 text-slate-300">
                  {dayTwo.map((item) => <li key={item}>- {item}</li>)}
                </ul>
              </div>
            </div>

            <div className="mt-8 rounded-xl border border-cyan-800/60 bg-cyan-950/20 p-5">
              <div className="font-bold text-cyan-100">Not ready for the paid workshop?</div>
              <p className="mt-2 text-sm leading-6 text-cyan-100/85">
                Join the free weekly Saturday webinar first, then come back when you want hands-on training.
              </p>
              <button
                onClick={() => router.push("/webinar/register")}
                className="mt-4 rounded-lg border border-cyan-700 px-4 py-2 text-sm font-semibold text-cyan-100 transition hover:bg-cyan-900/30"
              >
                Register for free webinar
              </button>
            </div>
          </section>

          <section className="rounded-2xl border border-slate-800 bg-white p-8 text-slate-950 shadow-2xl">
            {payment === "success" ? (
              <div className="flex min-h-[520px] flex-col justify-center">
                <div className="w-fit rounded-full bg-emerald-100 px-4 py-2 text-sm font-bold text-emerald-800">Payment received</div>
                <h2 className="mt-6 text-3xl font-extrabold">Your workshop seat is being confirmed.</h2>
                <p className="mt-4 leading-7 text-slate-600">
                  Stripe payment completed. Confirmation is finalized by the payment webhook.
                  {registration?.paid ? " Your registration is confirmed." : " If this page still says pending, refresh in a few seconds."}
                </p>
                {registration ? (
                  <div className="mt-5 rounded-lg border border-slate-200 bg-slate-50 p-4 text-sm text-slate-700">
                    <div>Registration: {registration.id}</div>
                    <div>Status: {registration.payment_status}</div>
                  </div>
                ) : null}
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
                  <h2 className="text-2xl font-extrabold">Reserve your workshop seat</h2>
                  <p className="mt-2 text-sm text-slate-600">Pay securely with Stripe. Your registration completes after payment.</p>
                </div>

                {payment === "cancelled" ? (
                  <div className="rounded-lg bg-amber-50 px-4 py-3 text-sm font-semibold text-amber-800">
                    Payment was cancelled. Your workshop seat is not reserved yet.
                  </div>
                ) : null}

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">Name</span>
                  <input required value={form.name} onChange={(event) => update("name", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500" placeholder="Your name" />
                </label>

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">Email</span>
                  <input required type="email" value={form.email} onChange={(event) => update("email", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500" placeholder="you@example.com" />
                </label>

                <div className="grid gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Company / School</span>
                    <input value={form.company} onChange={(event) => update("company", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500" placeholder="Optional" />
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Role</span>
                    <input value={form.role} onChange={(event) => update("role", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500" placeholder="Student, engineer, founder..." />
                  </label>
                </div>

                <div className="grid gap-4 sm:grid-cols-2">
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Loop interest</span>
                    <select value={form.loop_interest} onChange={(event) => update("loop_interest", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500">
                      {loopOptions.map((loop) => <option key={loop} value={loop}>{loop}</option>)}
                    </select>
                  </label>
                  <label className="block">
                    <span className="text-sm font-semibold text-slate-700">Workshop batch</span>
                    <select required value={form.batch_id} onChange={(event) => update("batch_id", event.target.value)} className="mt-2 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500">
                      {batchesLoading ? <option value="">Loading batches...</option> : null}
                      {!batchesLoading && !batches.length ? <option value="">No batches available</option> : null}
                      {batches.map((batch) => (
                        <option key={batch.id} value={batch.id} disabled={batch.full}>
                          {batchOptionLabel(batch)}
                        </option>
                      ))}
                    </select>
                    <p className="mt-2 text-xs text-slate-500">Each batch has 10 seats.</p>
                  </label>
                </div>

                <label className="block">
                  <span className="text-sm font-semibold text-slate-700">Questions or goals</span>
                  <textarea value={form.questions} onChange={(event) => update("questions", event.target.value)} className="mt-2 min-h-28 w-full rounded-lg border border-slate-300 px-4 py-3 outline-none focus:border-cyan-500" placeholder="Optional: tell us what you want to build" />
                </label>

                {error ? <div className="rounded-lg bg-red-50 px-4 py-3 text-sm font-semibold text-red-700">{error}</div> : null}

                <button disabled={loading || batchesLoading || !form.batch_id || Boolean(selectedBatch?.full)} className="w-full rounded-lg bg-cyan-500 px-5 py-3 font-bold text-slate-950 transition hover:bg-cyan-400 disabled:cursor-not-allowed disabled:bg-slate-300">
                  {loading ? "Opening Stripe..." : "Pay $99 and reserve seat"}
                </button>
              </form>
            )}
          </section>
        </div>
      </div>
    </main>
  );
}

export default function WorkshopPage() {
  return (
    <Suspense fallback={<div className="min-h-screen bg-slate-950 p-10 text-center text-white">Loading...</div>}>
      <WorkshopContent />
    </Suspense>
  );
}
