"use client";

import { useEffect, useMemo, useState } from "react";
import Link from "next/link";
import TopNav from "@/components/TopNav";
import { ApiClientError, apiGet, apiPost } from "@/lib/apiClient";
import { findHelpTopic, helpCategories, helpTopics, type HelpTopic } from "@/lib/helpContent";

type HelpAskResponse = {
  status: string;
  answer: string;
  suggested_actions: string[];
  sources: Array<{ slug: string; title: string; category: string; href: string }>;
};

type HelpCatalogRow = {
  type: "agent" | "workflow";
  name: string;
  loop_type: string;
  domain: string;
  description: string;
  steps: number | null;
};

type HelpCatalogResponse = {
  status: string;
  counts: {
    agents: number;
    workflows: number;
    agents_by_loop: Record<string, number>;
    workflows_by_loop: Record<string, number>;
  };
  rows: HelpCatalogRow[];
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

function renderHelpBodyLine(text: string) {
  const commandPrefixes = ["Command:", "macOS/Linux example:", "Windows PowerShell example:"];
  const commandPrefix = commandPrefixes.find((prefix) => text.startsWith(prefix));
  if (commandPrefix) {
    const command = text.slice(commandPrefix.length).trim();
    return (
      <div key={text} className="rounded-lg border border-slate-800 bg-slate-950/80 p-3">
        <p className="text-xs font-bold uppercase tracking-wide text-cyan-300">{commandPrefix.replace(":", "")}</p>
        <pre className="mt-2 overflow-x-auto whitespace-pre-wrap font-mono text-sm font-bold leading-6 text-cyan-100">
          {command}
        </pre>
      </div>
    );
  }

  const stepMatch = text.match(/^(Step \d+:)(.*)$/);
  if (stepMatch) {
    return (
      <p key={text}>
        <span className="font-bold text-white">{stepMatch[1]}</span>
        {stepMatch[2]}
      </p>
    );
  }

  return <p key={text}>{text}</p>;
}

export default function HelpPage() {
  const [selectedSlug, setSelectedSlug] = useState(helpTopics[0].slug);
  const [query, setQuery] = useState("");
  const [question, setQuestion] = useState("");
  const [answer, setAnswer] = useState<HelpAskResponse | null>(null);
  const [askError, setAskError] = useState<string | null>(null);
  const [asking, setAsking] = useState(false);
  const [catalog, setCatalog] = useState<HelpCatalogResponse | null>(null);
  const [catalogError, setCatalogError] = useState<string | null>(null);

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const topic = findHelpTopic(params.get("topic"));
    setSelectedSlug(topic.slug);
  }, []);

  useEffect(() => {
    if (selectedSlug !== "agent-workflow-catalog" || catalog || catalogError) return;
    let cancelled = false;
    apiGet<HelpCatalogResponse>("/help/catalog")
      .then((response) => {
        if (!cancelled) setCatalog(response);
      })
      .catch((error) => {
        if (!cancelled) setCatalogError(error instanceof Error ? error.message : "Catalog request failed.");
      });
    return () => {
      cancelled = true;
    };
  }, [catalog, catalogError, selectedSlug]);

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
            {selectedTopic.body.map((paragraph) => renderHelpBodyLine(paragraph))}
          </div>

          {selectedTopic.comparisonRows?.length ? (
            <div className="mt-6 overflow-hidden rounded-lg border border-slate-800">
              <div className="overflow-x-auto">
                <table className="min-w-[900px] divide-y divide-slate-800 text-left text-sm">
                  <thead className="bg-slate-950/80 text-xs font-semibold uppercase text-slate-400">
                    <tr>
                      <th scope="col" className="w-[16%] px-4 py-3">Area</th>
                      <th scope="col" className="w-[28%] px-4 py-3">Traditional Flow</th>
                      <th scope="col" className="w-[28%] px-4 py-3">ChipLoop Flow</th>
                      <th scope="col" className="w-[28%] px-4 py-3">Differentiation</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-800 bg-slate-950/40 text-slate-300">
                    {selectedTopic.comparisonRows.map((row) => (
                      <tr key={row.area} className="align-top">
                        <th scope="row" className="px-4 py-4 font-semibold text-cyan-100">{row.area}</th>
                        <td className="px-4 py-4">{row.traditional}</td>
                        <td className="px-4 py-4">{row.chiploop}</td>
                        <td className="px-4 py-4 font-medium text-white">{row.differentiation}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          ) : null}

          {selectedTopic.slug === "agent-workflow-catalog" ? (
            <div className="mt-6 space-y-4">
              {catalog ? (
                <>
                  <div className="grid gap-3 text-sm sm:grid-cols-2 lg:grid-cols-4">
                    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                      <p className="text-xs font-semibold uppercase text-slate-500">Agents</p>
                      <p className="mt-2 text-2xl font-bold text-white">{catalog.counts.agents}</p>
                    </div>
                    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                      <p className="text-xs font-semibold uppercase text-slate-500">Workflows</p>
                      <p className="mt-2 text-2xl font-bold text-white">{catalog.counts.workflows}</p>
                    </div>
                    <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 lg:col-span-2">
                      <p className="text-xs font-semibold uppercase text-slate-500">Agent loops</p>
                      <p className="mt-2 text-sm text-slate-300">
                        {Object.entries(catalog.counts.agents_by_loop).map(([loop, count]) => `${loop}: ${count}`).join(" | ")}
                      </p>
                    </div>
                  </div>
                  <div className="overflow-hidden rounded-lg border border-slate-800">
                    <div className="overflow-x-auto">
                      <table className="min-w-[980px] divide-y divide-slate-800 text-left text-sm">
                        <thead className="bg-slate-950/80 text-xs font-semibold uppercase text-slate-400">
                          <tr>
                            <th scope="col" className="w-[10%] px-4 py-3">Type</th>
                            <th scope="col" className="w-[10%] px-4 py-3">Loop</th>
                            <th scope="col" className="w-[24%] px-4 py-3">Name</th>
                            <th scope="col" className="w-[12%] px-4 py-3">Domain / Steps</th>
                            <th scope="col" className="w-[44%] px-4 py-3">Description</th>
                          </tr>
                        </thead>
                        <tbody className="divide-y divide-slate-800 bg-slate-950/40 text-slate-300">
                          {catalog.rows.map((row) => (
                            <tr key={`${row.type}:${row.name}`} className="align-top">
                              <td className="px-4 py-4 font-semibold text-cyan-100">{row.type}</td>
                              <td className="px-4 py-4">{row.loop_type || "unknown"}</td>
                              <th scope="row" className="px-4 py-4 font-semibold text-white">{row.name}</th>
                              <td className="px-4 py-4">{row.type === "workflow" ? `${row.steps ?? 0} agents` : row.domain}</td>
                              <td className="px-4 py-4">{row.description || "No description provided."}</td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </>
              ) : (
                <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">
                  {catalogError || "Loading registry catalog..."}
                </div>
              )}
            </div>
          ) : null}

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
