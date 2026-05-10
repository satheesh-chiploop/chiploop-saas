"use client";

import { useEffect, useMemo, useState } from "react";
import Link from "next/link";
import TopNav from "@/components/TopNav";
import { ApiClientError, apiPost } from "@/lib/apiClient";
import { findHelpTopic, helpCategories, helpTopics, type HelpTopic } from "@/lib/helpContent";

type HelpAskResponse = {
  status: string;
  answer: string;
  suggested_actions: string[];
  sources: Array<{ slug: string; title: string; category: string; href: string }>;
};

function topicMatches(topic: HelpTopic, query: string): boolean {
  const text = [
    topic.title,
    topic.category,
    topic.summary,
    ...topic.body,
    ...topic.actions,
    ...topic.exampleQuestions,
    ...topic.keywords,
  ].join(" ").toLowerCase();
  return text.includes(query.toLowerCase());
}

export default function HelpPage() {
  const [selectedSlug, setSelectedSlug] = useState(helpTopics[0].slug);
  const [query, setQuery] = useState("");
  const [question, setQuestion] = useState("");
  const [answer, setAnswer] = useState<HelpAskResponse | null>(null);
  const [askError, setAskError] = useState<string | null>(null);
  const [asking, setAsking] = useState(false);

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const topic = findHelpTopic(params.get("topic"));
    setSelectedSlug(topic.slug);
  }, []);

  const selectedTopic = findHelpTopic(selectedSlug);
  const visibleTopics = useMemo(() => {
    const trimmed = query.trim();
    if (!trimmed) return helpTopics;
    return helpTopics.filter((topic) => topicMatches(topic, trimmed));
  }, [query]);

  function selectTopic(slug: string) {
    setSelectedSlug(slug);
    const url = new URL(window.location.href);
    url.searchParams.set("topic", slug);
    window.history.replaceState(null, "", url.toString());
  }

  async function askHelp() {
    const trimmed = question.trim();
    if (!trimmed) {
      setAskError("Enter a question first.");
      return;
    }
    setAsking(true);
    setAskError(null);
    try {
      const response = await apiPost<HelpAskResponse>("/help/ask", { question: trimmed });
      setAnswer(response);
      if (response.sources[0]?.slug) {
        selectTopic(response.sources[0].slug);
      }
    } catch (error) {
      if (error instanceof ApiClientError && error.status === 401) {
        setAskError("Log in to use Ask ChipLoop Help.");
      } else if (error instanceof Error) {
        setAskError(error.message);
      } else {
        setAskError("Help request failed.");
      }
    } finally {
      setAsking(false);
    }
  }

  return (
    <main className="min-h-screen bg-slate-950 text-slate-100">
      <TopNav current="help" showMarketplace showPlanBadge maxWidthClass="max-w-7xl" />

      <section className="mx-auto flex max-w-7xl flex-col gap-6 px-4 py-8 sm:px-6 lg:grid lg:grid-cols-[280px_1fr_360px]">
        <aside className="rounded-lg border border-slate-800 bg-slate-900/70 p-4">
          <div className="mb-4">
            <p className="text-xs font-semibold uppercase tracking-wide text-cyan-300">User Guide</p>
            <h1 className="mt-2 text-2xl font-bold text-white">ChipLoop Help</h1>
            <p className="mt-2 text-sm text-slate-400">Find the workflow, integration, and inspection steps users need.</p>
          </div>

          <label className="text-xs font-semibold uppercase tracking-wide text-slate-400" htmlFor="help-search">
            Search
          </label>
          <input
            id="help-search"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            placeholder="Apps, GitHub, Ask This Run..."
            className="mt-2 w-full rounded-md border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-100 outline-none transition focus:border-cyan-400"
          />

          <div className="mt-5 space-y-4">
            {helpCategories.map((category) => {
              const topics = visibleTopics.filter((topic) => topic.category === category);
              if (!topics.length) return null;
              return (
                <div key={category}>
                  <p className="mb-2 text-xs font-semibold uppercase tracking-wide text-slate-500">{category}</p>
                  <div className="space-y-1">
                    {topics.map((topic) => (
                      <button
                        key={topic.slug}
                        type="button"
                        onClick={() => selectTopic(topic.slug)}
                        className={`w-full rounded-md px-3 py-2 text-left text-sm transition ${
                          selectedTopic.slug === topic.slug
                            ? "bg-cyan-400/15 font-semibold text-cyan-100"
                            : "text-slate-300 hover:bg-slate-800 hover:text-white"
                        }`}
                      >
                        {topic.title}
                      </button>
                    ))}
                  </div>
                </div>
              );
            })}
          </div>
        </aside>

        <article className="rounded-lg border border-slate-800 bg-slate-900/60 p-5 sm:p-6">
          <div className="border-b border-slate-800 pb-5">
            <p className="text-sm font-semibold text-cyan-300">{selectedTopic.category}</p>
            <h2 className="mt-2 text-3xl font-bold text-white">{selectedTopic.title}</h2>
            <p className="mt-3 text-base text-slate-300">{selectedTopic.summary}</p>
          </div>

          <div className="mt-6 space-y-4 text-sm leading-6 text-slate-300">
            {selectedTopic.body.map((paragraph) => (
              <p key={paragraph}>{paragraph}</p>
            ))}
          </div>

          <div className="mt-7 grid gap-4 md:grid-cols-2">
            <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <h3 className="text-sm font-semibold text-white">What to do</h3>
              <ul className="mt-3 space-y-2 text-sm text-slate-300">
                {selectedTopic.actions.map((action) => (
                  <li key={action} className="flex gap-2">
                    <span className="mt-2 h-1.5 w-1.5 shrink-0 rounded-full bg-cyan-300" />
                    <span>{action}</span>
                  </li>
                ))}
              </ul>
            </section>

            <section className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <h3 className="text-sm font-semibold text-white">Open in ChipLoop</h3>
              <div className="mt-3 flex flex-wrap gap-2">
                {selectedTopic.links.map((link) => (
                  <Link
                    key={link.href}
                    href={link.href}
                    className="rounded-md border border-slate-700 px-3 py-2 text-sm font-semibold text-cyan-200 transition hover:border-cyan-400 hover:bg-cyan-400/10"
                  >
                    {link.label}
                  </Link>
                ))}
              </div>
            </section>
          </div>

        </article>

        <aside className="rounded-lg border border-cyan-400/30 bg-cyan-950/20 p-4">
          <p className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Ask ChipLoop Help</p>
          <h2 className="mt-2 text-xl font-bold text-white">Get a quick answer</h2>
          <p className="mt-2 text-sm text-slate-300">
            Ask about Apps, Studio, GitHub, CLI, SDK, agents, or run inspection.
          </p>

          <textarea
            value={question}
            onChange={(event) => setQuestion(event.target.value)}
            placeholder="Example: How do I import GitHub context into Studio?"
            className="mt-4 min-h-28 w-full resize-y rounded-md border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-slate-100 outline-none transition focus:border-cyan-400"
          />
          <div className="mt-3">
            <p className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Example questions</p>
            <div className="mt-2 flex flex-wrap gap-2">
              {selectedTopic.exampleQuestions.map((sample) => (
                <button
                  key={sample}
                  type="button"
                  onClick={() => setQuestion(sample)}
                  className="rounded-md bg-slate-800 px-3 py-2 text-left text-xs text-slate-200 transition hover:bg-slate-700"
                >
                  {sample}
                </button>
              ))}
            </div>
          </div>
          <button
            type="button"
            onClick={askHelp}
            disabled={asking}
            className="mt-3 w-full rounded-md bg-cyan-300 px-4 py-2 text-sm font-bold text-slate-950 transition hover:bg-cyan-200 disabled:cursor-not-allowed disabled:opacity-60"
          >
            {asking ? "Asking..." : "Ask Help"}
          </button>

          {askError ? <p className="mt-3 rounded-md border border-red-500/30 bg-red-950/30 p-3 text-sm text-red-200">{askError}</p> : null}

          {answer ? (
            <section className="mt-4 rounded-lg border border-slate-800 bg-slate-950/70 p-4">
              <p className="text-sm leading-6 text-slate-200">{answer.answer}</p>
              <div className="mt-4">
                <p className="text-xs font-semibold uppercase tracking-wide text-slate-500">Suggested actions</p>
                <ul className="mt-2 space-y-2 text-sm text-slate-300">
                  {answer.suggested_actions.map((action) => (
                    <li key={action}>{action}</li>
                  ))}
                </ul>
              </div>
              <div className="mt-4 flex flex-wrap gap-2">
                {answer.sources.map((source) => (
                  <button
                    key={source.slug}
                    type="button"
                    onClick={() => selectTopic(source.slug)}
                    className="rounded-md border border-slate-700 px-3 py-2 text-xs font-semibold text-cyan-200 transition hover:border-cyan-400"
                  >
                    {source.title}
                  </button>
                ))}
              </div>
            </section>
          ) : null}
        </aside>
      </section>
    </main>
  );
}
