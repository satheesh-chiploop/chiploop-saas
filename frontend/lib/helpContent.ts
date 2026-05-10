export type HelpTopic = {
  slug: string;
  title: string;
  category: "Basics" | "Apps" | "Inspection" | "Studio" | "Integrations" | "Developer" | "Examples";
  summary: string;
  body: string[];
  actions: string[];
  exampleQuestions: string[];
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
    exampleQuestions: [
      "What should I try first in ChipLoop?",
      "Should I start with Apps or Studio?",
      "How do I inspect a completed demo run?",
    ],
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
    exampleQuestions: [
      "What does Arch2RTL generate?",
      "What should I put in the Arch2RTL requirement?",
      "How do I review the Arch2RTL outputs?",
    ],
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
    exampleQuestions: [
      "When does Ask This Run appear?",
      "Can Ask This Run summarize reports and logs?",
      "What questions should I ask after a failed run?",
    ],
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
      "The main Studio building blocks are workflows, agents, design intent, and integrations. A workflow connects agents into an execution path. Agents perform scoped engineering tasks. Design intent records reusable requirements, constraints, and assumptions that should guide generation and review.",
    ],
    actions: ["Open Studio", "Choose Prebuilt or create a workflow", "Preview and validate the graph before running"],
    exampleQuestions: [
      "What is a workflow in Studio?",
      "How do agents connect inside a workflow?",
      "How should I use design intent in Studio?",
    ],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["studio", "workflow", "prebuilt", "graph", "nodes", "edges", "planner", "agents", "design intent"],
  },
  {
    slug: "system-planner",
    title: "System Planner",
    category: "Studio",
    summary: "Use System Planner to turn a system-level goal into an executable multi-agent workflow.",
    body: [
      "System Planner is for users who know the desired system outcome but need ChipLoop to structure the work. It helps translate requirements into workflow steps, agents, inputs, outputs, and review points.",
      "Use it when the problem spans RTL, firmware, validation, integration, or multiple artifacts rather than one isolated generation task.",
    ],
    actions: ["Open Studio", "Choose System Planner", "Describe the system goal, constraints, and expected outputs"],
    exampleQuestions: [
      "When should I use System Planner instead of Agent Planner?",
      "What should I write in a System Planner requirement?",
      "Can System Planner create a multi-agent workflow?",
    ],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["system planner", "system", "planner", "multi-agent", "requirements", "workflow"],
  },
  {
    slug: "design-intent-analyzer",
    title: "Design Intent Analyzer",
    category: "Studio",
    summary: "Use Design Intent Analyzer to extract requirements, constraints, assumptions, and verification intent.",
    body: [
      "Design Intent Analyzer helps convert unstructured specs, notes, or repository context into reusable design intent. It is useful before generation because it makes hidden assumptions explicit.",
      "The output should help guide agents, improve workflow quality, and give reviewers a clearer checklist for what the run should preserve.",
    ],
    actions: ["Open Studio", "Run Design Intent Analyzer on specs or repo context", "Save useful intent into the design intent library"],
    exampleQuestions: [
      "What does Design Intent Analyzer extract?",
      "How is design intent different from a prompt?",
      "How do I reuse design intent in a workflow?",
    ],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["design intent", "analyzer", "requirements", "constraints", "assumptions", "library", "spec"],
  },
  {
    slug: "optimize-workflow",
    title: "Optimize Workflow",
    category: "Studio",
    summary: "Use Optimize Workflow to improve a draft workflow before running or re-running it.",
    body: [
      "Optimize Workflow reviews a workflow graph and suggests improvements to ordering, missing agents, handoff artifacts, and inspection points.",
      "Use it when a workflow is too vague, has weak connections between agents, or needs stronger validation before execution.",
    ],
    actions: ["Open an existing workflow", "Run Optimize Workflow", "Review suggested changes before saving or running"],
    exampleQuestions: [
      "When should I optimize a workflow?",
      "What can Optimize Workflow improve?",
      "How do I know if my workflow is ready to run?",
    ],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["optimize", "workflow", "graph", "validation", "handoff", "agents"],
  },
  {
    slug: "design-intent-library",
    title: "Design Intent Library",
    category: "Studio",
    summary: "Keep reusable requirements, constraints, assumptions, and review intent in one place.",
    body: [
      "The design intent library is where users should store reusable engineering intent instead of rewriting it for every run. It can include interface rules, reset assumptions, power constraints, verification goals, and style preferences.",
      "Use the library to make future workflows more consistent and easier to inspect.",
    ],
    actions: ["Capture intent from specs or analysis", "Save it with a clear name", "Attach relevant intent to future workflows"],
    exampleQuestions: [
      "What belongs in the design intent library?",
      "How should I name design intent entries?",
      "Can design intent be reused across workflows?",
    ],
    links: [{ label: "Studio", href: "/workflow" }],
    keywords: ["design intent library", "library", "constraints", "requirements", "reuse", "intent"],
  },
  {
    slug: "marketplace",
    title: "Marketplace",
    category: "Studio",
    summary: "Use Marketplace to discover agents and workflow building blocks beyond your private workspace.",
    body: [
      "Marketplace is where reusable agents and capabilities can be discovered. Private agents start scoped to the user, while marketplace items are intended for broader reuse after review.",
      "Use Marketplace when a workflow needs an agent you do not want to create from scratch, or when you want to install a reusable building block into Studio.",
    ],
    actions: ["Open Marketplace", "Review the agent capability and inputs", "Install or use it in a Studio workflow"],
    exampleQuestions: [
      "When should I use Marketplace?",
      "What is the difference between a private agent and Marketplace agent?",
      "How do I add a Marketplace agent to Studio?",
    ],
    links: [
      { label: "Marketplace", href: "/marketplace" },
      { label: "Studio", href: "/workflow" },
    ],
    keywords: ["marketplace", "agent", "install", "private", "public", "reuse"],
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
    exampleQuestions: [
      "How do I create a private agent?",
      "What fields should I fill for a new agent?",
      "Can I edit an agent after it is generated?",
    ],
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
    exampleQuestions: [
      "How do I connect GitHub?",
      "Can each user connect their own GitHub?",
      "How do I import repository context into Studio?",
    ],
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
    exampleQuestions: [
      "How do I create an API key?",
      "What is the CLI or SDK flow?",
      "How do I keep API keys safe?",
    ],
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
    exampleQuestions: [
      "Can you give me a PWM Arch2RTL example?",
      "What should I ask after the PWM run finishes?",
      "What should be verified in the PWM output?",
    ],
    links: [{ label: "Arch2RTL", href: "/apps/arch2rtl" }],
    keywords: ["example", "pwm", "controller", "arch2rtl", "simulation", "verification"],
  },
];

export const helpCategories = ["Basics", "Apps", "Inspection", "Studio", "Integrations", "Developer", "Examples"] as const;

export function findHelpTopic(slug: string | null): HelpTopic {
  return helpTopics.find((topic) => topic.slug === slug) || helpTopics[0];
}
