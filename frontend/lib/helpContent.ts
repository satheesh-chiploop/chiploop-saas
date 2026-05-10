export type HelpTopic = {
  slug: string;
  title: string;
  category: "Basics" | "Apps" | "Inspection" | "Studio" | "Integrations" | "Developer" | "Examples";
  summary: string;
  body: string[];
  actions: string[];
  links: Array<{ label: string; href: string }>;
  keywords: string[];
};

export const helpTopics: HelpTopic[] = [
  {
    slug: "getting-started",
    title: "Getting Started",
    category: "Basics",
    summary: "Start with Apps for guided flows or Studio for custom workflows.",
    body: [
      "ChipLoop has two main work areas. Apps are guided workflows such as Arch2RTL. Studio is where users compose, inspect, and run agent workflows.",
      "A good first path is Apps, Arch2RTL, run the demo, then use Ask This Run after completion to inspect generated artifacts and logs.",
    ],
    actions: ["Open Apps", "Run the Arch2RTL demo", "Ask This Run after the workflow finishes"],
    links: [
      { label: "Apps", href: "/apps" },
      { label: "Studio", href: "/workflow" },
    ],
    keywords: ["start", "begin", "onboarding", "apps", "studio", "demo"],
  },
  {
    slug: "apps-arch2rtl",
    title: "Apps and Arch2RTL",
    category: "Apps",
    summary: "Use Arch2RTL to turn a structured design requirement into RTL-oriented outputs.",
    body: [
      "Apps are the fastest way to run a prebuilt ChipLoop flow. Arch2RTL accepts a design requirement and produces workflow artifacts for RTL handoff.",
      "After a run completes, downloads and Ask This Run become available so users can inspect what was generated.",
    ],
    actions: ["Go to Apps", "Choose Arch2RTL", "Review outputs and Ask This Run"],
    links: [
      { label: "Apps", href: "/apps" },
      { label: "Arch2RTL", href: "/apps/arch2rtl" },
    ],
    keywords: ["arch2rtl", "apps", "demo", "rtl", "download", "artifacts"],
  },
  {
    slug: "ask-this-run",
    title: "Ask This Run",
    category: "Inspection",
    summary: "Ask run-specific questions using logs, metadata, and text artifacts from a completed workflow.",
    body: [
      "Ask This Run appears after a run finishes. It helps users inspect generated reports, logs, and artifacts without manually opening every file.",
      "Good questions include: What was generated? What failed? Summarize the RTL handoff. List missing signals. What should I check next?",
    ],
    actions: ["Wait for the run to finish", "Open Ask This Run", "Ask a specific question about the outputs"],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["ask", "inspection", "logs", "reports", "artifacts", "summarize", "run"],
  },
  {
    slug: "studio-workflows",
    title: "Studio Workflows",
    category: "Studio",
    summary: "Studio is for composing, previewing, validating, and running agent workflows.",
    body: [
      "Studio shows prebuilt workflows and user-created workflows. Prebuilt workflows can be opened as a starting point and then adapted.",
      "Use the planner when the workflow needs a new agent or a different execution graph. Preview and validate the graph before running it.",
    ],
    actions: ["Open Studio", "Choose Prebuilt or create a workflow", "Preview and validate the graph before running"],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["studio", "workflow", "prebuilt", "graph", "nodes", "edges", "planner"],
  },
  {
    slug: "agent-planner",
    title: "Agent Planner",
    category: "Studio",
    summary: "Plan a private agent from requirements, then review and save it.",
    body: [
      "Agent Planner takes requirements and can create a private agent draft. Private agents start scoped to the user and can be edited before use.",
      "For a new agent, define the goal, input artifacts, output artifacts, one skill, one MCP/tool connection, and any hooks needed before or after execution.",
    ],
    actions: ["Open Studio", "Select Agent Planner", "Check Create new private agent when you want a fresh draft"],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["agent", "planner", "private", "skill", "mcp", "hook", "template"],
  },
  {
    slug: "github",
    title: "GitHub Integration",
    category: "Integrations",
    summary: "Connect your own GitHub account, then import repository context into Apps or Studio.",
    body: [
      "Each user installs the ChipLoop GitHub App for their own account or organization. The administrator configures the app once; users authorize their own installations.",
      "After connection, users can import repository files into a workflow prompt or Studio context. Repository access is scoped by the GitHub installation permissions.",
    ],
    actions: ["Open Settings, Integrations", "Connect GitHub", "Import selected repository context into Apps or Studio"],
    links: [{ label: "GitHub settings", href: "/settings/integrations" }],
    keywords: ["github", "repository", "repo", "install", "integration", "settings", "import"],
  },
  {
    slug: "cli-sdk",
    title: "CLI and SDK",
    category: "Developer",
    summary: "Use API keys for scripted access once the account and plan are ready.",
    body: [
      "Developer access uses API keys created in Settings. Keep keys private and revoke keys that are no longer used.",
      "The normal flow is create an API key, call backend workflow endpoints from a script or SDK client, then inspect outputs in the platform.",
    ],
    actions: ["Open Settings, API Keys", "Create a scoped key", "Use the key from CLI or SDK automation"],
    links: [{ label: "API keys", href: "/settings/api-keys" }],
    keywords: ["cli", "sdk", "api", "api key", "automation", "developer"],
  },
  {
    slug: "example-pwm",
    title: "Example: PWM Controller",
    category: "Examples",
    summary: "A simple Arch2RTL example for a PWM controller.",
    body: [
      "Ask Arch2RTL to design a parameterized PWM controller with clk, reset_n, enable, duty_cycle[7:0], period[7:0], pwm_out, and counter_value[7:0].",
      "After the run completes, ask: summarize the generated RTL, list the reset behavior, and what should be verified in simulation.",
    ],
    actions: ["Paste the PWM requirement into Arch2RTL", "Run the workflow", "Use Ask This Run for the verification checklist"],
    links: [{ label: "Arch2RTL", href: "/apps/arch2rtl" }],
    keywords: ["example", "pwm", "controller", "arch2rtl", "simulation", "verification"],
  },
];

export const helpCategories = ["Basics", "Apps", "Inspection", "Studio", "Integrations", "Developer", "Examples"] as const;

export function findHelpTopic(slug: string | null): HelpTopic {
  return helpTopics.find((topic) => topic.slug === slug) || helpTopics[0];
}
