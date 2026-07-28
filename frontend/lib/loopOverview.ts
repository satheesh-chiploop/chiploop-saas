export type LoopOverview = {
  name: string;
  eyebrow: string;
  promise: string;
  description: string;
  accent: string;
  accentText: string;
  accentBorder: string;
  inputs: string[];
  stages: Array<{ label: string; detail: string }>;
  outcomes: string[];
  starts: Array<{ title: string; body: string; label: string; href: string }>;
  workflow: string;
  apps: Array<{ name: string; description: string; href: string }>;
  agentGroups: Array<{ name: string; description: string }>;
  reference: {
    title: string;
    description: string;
    href: string;
    results: Array<{ label: string; value: number }>;
  };
};

const digital: LoopOverview = {
  name: "Digital Design",
  eyebrow: "From idea to trustworthy RTL",
  promise: "Turn a design idea into implementation-ready, verified RTL.",
  description: "Describe the behavior you need or bring existing RTL. ChipLoop organizes the design, quality, and verification work around it.",
  accent: "bg-cyan-400",
  accentText: "text-cyan-200",
  accentBorder: "border-cyan-400/45",
  inputs: ["Your design intent", "Existing RTL, if available", "The behavior that must be proven"],
  stages: [
    { label: "Understand", detail: "Turn requirements into a clear design contract." },
    { label: "Design", detail: "Create or improve synthesizable RTL." },
    { label: "Verify", detail: "Check quality, behavior, assertions, and coverage." },
    { label: "Handoff", detail: "Package evidence for implementation." },
  ],
  outcomes: ["Synthesizable RTL", "Quality and verification evidence", "Constraints and implementation handoff"],
  starts: [
    { title: "Start from an idea", body: "Describe the block you want ChipLoop to build.", label: "Create RTL", href: "/apps/arch2rtl" },
    { title: "Bring existing RTL", body: "Review quality, risks, and readiness.", label: "Review RTL", href: "/apps/rtl-review" },
    { title: "Verify a design", body: "Run simulation and verification evidence.", label: "Start verification", href: "/apps/verify" },
  ],
  workflow: "Intent becomes a design contract, RTL, quality checks, verification evidence, and a clean downstream handoff.",
  apps: [
    { name: "Architecture to RTL", description: "Create RTL and implementation intent from a specification.", href: "/apps/arch2rtl" },
    { name: "RTL Review", description: "Assess existing RTL quality and readiness.", href: "/apps/rtl-review" },
    { name: "Verify", description: "Build and run the verification plan.", href: "/apps/verify" },
  ],
  agentGroups: [
    { name: "Design", description: "Understands intent and develops RTL." },
    { name: "Quality", description: "Finds structural and coding risks." },
    { name: "Verification", description: "Builds tests, assertions, and evidence." },
  ],
  reference: {
    title: "PWM Controller",
    description: "See a compact design move from intent through RTL and verification.",
    href: "/apps#reference-journeys",
    results: [{ label: "Intent", value: 100 }, { label: "RTL", value: 100 }, { label: "Quality", value: 94 }, { label: "Verify", value: 90 }],
  },
};

const implementation: LoopOverview = {
  name: "Digital Implementation",
  eyebrow: "From RTL to implementation evidence",
  promise: "Move RTL through synthesis, closure, signoff, and tapeout handoff.",
  description: "Provide implementation-ready RTL and your targets. ChipLoop coordinates the tools, diagnoses misses, and keeps the evidence connected.",
  accent: "bg-violet-400",
  accentText: "text-violet-200",
  accentBorder: "border-violet-400/45",
  inputs: ["Implementation-ready RTL", "Clock and design constraints", "Technology or implementation target"],
  stages: [
    { label: "Prepare", detail: "Check RTL, constraints, and tool readiness." },
    { label: "Implement", detail: "Run synthesis and physical implementation." },
    { label: "Close", detail: "Diagnose timing, power, and area misses." },
    { label: "Sign off", detail: "Collect final checks and handoff evidence." },
  ],
  outcomes: ["Synthesis and implementation reports", "Closure decisions and reproducible settings", "Signoff or tapeout handoff"],
  starts: [
    { title: "Synthesize RTL", body: "Generate mapped implementation evidence.", label: "Start synthesis", href: "/apps/arch2synthesis" },
    { title: "Debug timing", body: "Understand and address timing violations.", label: "Open timing debug", href: "/apps/timing-debug" },
    { title: "Run to tapeout", body: "Connect implementation and signoff stages.", label: "Start implementation", href: "/apps/arch2tapeout" },
  ],
  workflow: "ChipLoop checks the handoff, runs implementation, diagnoses closure misses, and preserves the evidence needed for an engineering decision.",
  apps: [
    { name: "Architecture to Synthesis", description: "Synthesize RTL and review timing, power, and area.", href: "/apps/arch2synthesis" },
    { name: "Timing Debug", description: "Group and diagnose critical timing paths.", href: "/apps/timing-debug" },
    { name: "Architecture to Tapeout", description: "Run implementation and signoff as a connected journey.", href: "/apps/arch2tapeout" },
  ],
  agentGroups: [
    { name: "Preparation", description: "Checks constraints, readiness, and inputs." },
    { name: "Implementation", description: "Runs synthesis and physical-design stages." },
    { name: "Closure and signoff", description: "Diagnoses misses and verifies final evidence." },
  ],
  reference: {
    title: "SRAM MBIST to implementation",
    description: "Inspect a reference memory design with DFT and implementation evidence.",
    href: "/apps#reference-journeys",
    results: [{ label: "RTL", value: 100 }, { label: "Synthesis", value: 94 }, { label: "Closure", value: 86 }, { label: "Signoff", value: 78 }],
  },
};

const fpga: LoopOverview = {
  name: "FPGA Prototyping",
  eyebrow: "From idea to board-ready bitstream",
  promise: "Build, verify, and implement your idea on the right FPGA.",
  description: "Choose a board when you know it, or compare supported targets first. ChipLoop handles the implementation details and reports what matters.",
  accent: "bg-lime-300",
  accentText: "text-lime-200",
  accentBorder: "border-lime-300/45",
  inputs: ["Your design idea or RTL", "A target frequency", "A board—or boards to compare"],
  stages: [
    { label: "Describe", detail: "Capture behavior, interfaces, and target clock." },
    { label: "Choose", detail: "Select a board or compare suitable targets." },
    { label: "Build", detail: "Generate and verify FPGA-ready RTL." },
    { label: "Implement", detail: "Synthesize, place, route, and close timing." },
    { label: "Deliver", detail: "Package bitstream and reproducible evidence." },
  ],
  outcomes: ["Verified FPGA design", "Timing and utilization results", "Board-ready bitstream and reproducible configuration"],
  starts: [
    { title: "Start from an idea", body: "Generate FPGA-ready RTL and continue to implementation.", label: "Start prototyping", href: "/apps/fpga2rtl?reference=pwm" },
    { title: "Bring existing RTL", body: "Verify and implement a design you already have.", label: "Implement RTL", href: "/apps/fpga-bitstream" },
    { title: "Compare boards", body: "Sweep selected targets and choose the best fit.", label: "Explore boards", href: "/apps/fpga-target-explorer?reference=minirv" },
  ],
  workflow: "ChipLoop verifies the design, applies board constraints, explores implementation settings when needed, and locks the configuration that meets the target.",
  apps: [
    { name: "FPGA Prototyping", description: "Go from design intent to verified RTL and bitstream.", href: "/apps/fpga2rtl?reference=pwm" },
    { name: "FPGA Target Explorer", description: "Compare selected boards using the same design.", href: "/apps/fpga-target-explorer?reference=minirv" },
    { name: "FPGA Verify", description: "Check simulation, assertions, and coverage.", href: "/apps/fpga-verify" },
  ],
  agentGroups: [
    { name: "Design and quality", description: "Creates FPGA-ready RTL and checks it." },
    { name: "Verification", description: "Confirms behavior and coverage." },
    { name: "Implementation and closure", description: "Runs synthesis, P&R, timing closure, and packaging." },
  ],
  reference: {
    title: "PWM FPGA prototype",
    description: "Follow a PWM controller from intent to a downloadable bitstream.",
    href: "/apps/fpga2rtl?reference=pwm",
    results: [{ label: "RTL", value: 100 }, { label: "Verify", value: 94 }, { label: "Implement", value: 88 }, { label: "Bitstream", value: 100 }],
  },
};

function domainLoop(overrides: Partial<LoopOverview> & Pick<LoopOverview, "name" | "eyebrow" | "promise">): LoopOverview {
  return {
    ...digital,
    ...overrides,
  };
}

const analog = domainLoop({
  name: "Analog Design",
  eyebrow: "From specification to correlated model",
  promise: "Turn analog requirements into reviewable designs, simulations, and models.",
  description: "Provide the behavior and operating limits. ChipLoop connects specifications, simulation evidence, and model validation.",
  accent: "bg-fuchsia-400", accentText: "text-fuchsia-200", accentBorder: "border-fuchsia-400/45",
  inputs: ["Performance requirements", "Operating conditions", "A schematic, netlist, or model if available"],
  stages: [
    { label: "Specify", detail: "Make requirements and corners explicit." },
    { label: "Design", detail: "Develop or review the circuit approach." },
    { label: "Simulate", detail: "Measure behavior across relevant conditions." },
    { label: "Correlate", detail: "Compare results and improve the model." },
  ],
  outcomes: ["Clear analog specification", "Simulation and corner evidence", "Validated behavioral-model handoff"],
  starts: [
    { title: "Define requirements", body: "Turn product intent into an analog specification.", label: "Create specification", href: "/apps/analog-spec" },
    { title: "Analyze a netlist", body: "Review an existing analog implementation.", label: "Analyze netlist", href: "/apps/analog-netlist" },
    { title: "Validate a model", body: "Compare model behavior with expected results.", label: "Validate model", href: "/apps/analog-validate-model" },
  ],
  workflow: "Requirements guide design and simulation; results are correlated into a model and evidence package suitable for system integration.",
  apps: [
    { name: "Analog Specification", description: "Create measurable requirements and corner intent.", href: "/apps/analog-spec" },
    { name: "Analog Run", description: "Execute and summarize analog simulation evidence.", href: "/apps/analog-run" },
    { name: "Model Validation", description: "Validate behavioral-model results.", href: "/apps/analog-validate-model" },
  ],
  agentGroups: [
    { name: "Specification", description: "Structures requirements and operating conditions." },
    { name: "Simulation", description: "Runs measurements and reviews results." },
    { name: "Correlation", description: "Compares evidence and improves model fidelity." },
  ],
  reference: { title: "Temperature sensor model", description: "See an analog sensor model prepared for integration.", href: "/apps#reference-journeys", results: [{ label: "Spec", value: 100 }, { label: "Model", value: 92 }, { label: "Corners", value: 84 }, { label: "Correlate", value: 90 }] },
});

const mixedSignal = domainLoop({
  name: "Mixed Signal",
  eyebrow: "Connect digital and analog behavior",
  promise: "Integrate RTL, analog models, and system behavior into one journey.",
  description: "Bring the digital and analog intent. ChipLoop coordinates integration, simulation, diagnosis, and downstream handoffs.",
  accent: "bg-rose-400", accentText: "text-rose-200", accentBorder: "border-rose-400/45",
  inputs: ["System behavior and interfaces", "Digital RTL or intent", "Analog model or specification"],
  stages: [
    { label: "Connect", detail: "Align interfaces and integration intent." },
    { label: "Model", detail: "Prepare digital and analog behavior." },
    { label: "Simulate", detail: "Exercise the integrated system." },
    { label: "Improve", detail: "Diagnose mismatches and update the handoff." },
  ],
  outcomes: ["Integrated system model", "Cross-domain simulation evidence", "Firmware, implementation, and validation handoffs"],
  starts: [
    { title: "Start a system", body: "Describe the complete product behavior.", label: "Build architecture", href: "/apps/system-architecture" },
    { title: "Integrate designs", body: "Connect existing digital and analog work.", label: "Start integration", href: "/apps/integrate" },
    { title: "Run the system", body: "Simulate and inspect cross-domain behavior.", label: "Run simulation", href: "/apps/system-sim" },
  ],
  workflow: "ChipLoop aligns interfaces, prepares models, runs integrated behavior, and turns findings into actionable domain handoffs.",
  apps: [
    { name: "System Architecture", description: "Define the product and cross-domain interfaces.", href: "/apps/system-architecture" },
    { name: "Integrate", description: "Connect digital, analog, and system collateral.", href: "/apps/integrate" },
    { name: "System Simulation", description: "Run and inspect integrated behavior.", href: "/apps/system-sim" },
  ],
  agentGroups: [
    { name: "System", description: "Owns interfaces and end-to-end intent." },
    { name: "Digital and analog", description: "Prepares domain designs and models." },
    { name: "Integration", description: "Runs co-simulation and diagnoses mismatches." },
  ],
  reference: { title: "Temperature Monitor SoC", description: "See sensing, control, firmware, and validation connected.", href: "/apps#reference-journeys", results: [{ label: "Models", value: 100 }, { label: "Integrate", value: 94 }, { label: "Simulate", value: 88 }, { label: "Handoff", value: 82 }] },
});

const firmware = domainLoop({
  name: "Firmware / Software",
  eyebrow: "From hardware interface to working software",
  promise: "Build drivers, firmware, diagnostics, and software around your hardware.",
  description: "Provide hardware interfaces and desired behavior. ChipLoop generates the software layers, validates them, and keeps hardware context attached.",
  accent: "bg-emerald-400", accentText: "text-emerald-200", accentBorder: "border-emerald-400/45",
  inputs: ["Register or interface definition", "Target platform", "Expected software behavior"],
  stages: [
    { label: "Understand", detail: "Extract interfaces and required behavior." },
    { label: "Build", detail: "Create HAL, drivers, firmware, or services." },
    { label: "Run", detail: "Build and exercise the software." },
    { label: "Diagnose", detail: "Use logs and evidence to improve it." },
  ],
  outcomes: ["HAL, drivers, or firmware", "Build and diagnostic evidence", "Validated software handoff"],
  starts: [
    { title: "Create a HAL", body: "Generate a clean hardware abstraction layer.", label: "Build HAL", href: "/apps/embedded-hal" },
    { title: "Build a driver", body: "Implement a hardware-facing driver.", label: "Build driver", href: "/apps/embedded-driver" },
    { title: "Diagnose firmware", body: "Turn runtime evidence into fixes.", label: "Start diagnostics", href: "/apps/embedded-diagnostics" },
  ],
  workflow: "Hardware context becomes software interfaces, executable code, runtime evidence, and an improved implementation.",
  apps: [
    { name: "Embedded HAL", description: "Generate the hardware abstraction layer.", href: "/apps/embedded-hal" },
    { name: "Embedded Driver", description: "Create a driver from hardware intent.", href: "/apps/embedded-driver" },
    { name: "Firmware Diagnostics", description: "Analyze runtime problems and propose repairs.", href: "/apps/embedded-diagnostics" },
  ],
  agentGroups: [
    { name: "Interface", description: "Understands registers and hardware behavior." },
    { name: "Implementation", description: "Builds HAL, drivers, and firmware." },
    { name: "Runtime quality", description: "Validates builds, logs, and diagnostics." },
  ],
  reference: { title: "PWM firmware and software", description: "See hardware intent carried into a product-facing app.", href: "/apps#reference-journeys", results: [{ label: "Interface", value: 100 }, { label: "Driver", value: 95 }, { label: "Build", value: 90 }, { label: "Validate", value: 86 }] },
});

const validation = domainLoop({
  name: "Validation",
  eyebrow: "From plan to evidence-driven learning",
  promise: "Plan, run, and improve hardware validation with connected evidence.",
  description: "Define what must be proven and describe the bench. ChipLoop organizes execution, results, coverage, and the next action.",
  accent: "bg-amber-300", accentText: "text-amber-200", accentBorder: "border-amber-300/45",
  inputs: ["Validation goals", "Device and bench context", "Existing tests or results, if available"],
  stages: [
    { label: "Plan", detail: "Turn goals into measurable validation intent." },
    { label: "Prepare", detail: "Check bench, instruments, and connectivity." },
    { label: "Run", detail: "Execute tests and collect evidence." },
    { label: "Learn", detail: "Summarize coverage, failures, and next actions." },
  ],
  outcomes: ["Actionable validation plan", "Traceable execution results", "Coverage, diagnosis, and recommendations"],
  starts: [
    { title: "Create a plan", body: "Turn product goals into validation coverage.", label: "Plan validation", href: "/apps/validation-plan" },
    { title: "Prepare the bench", body: "Check instruments and execution readiness.", label: "Set up bench", href: "/apps/bench-setup" },
    { title: "Analyze results", body: "Understand failures, gaps, and next steps.", label: "View insights", href: "/apps/validation-insights" },
  ],
  workflow: "Validation intent becomes a bench-ready plan, controlled execution, traceable evidence, and prioritized improvements.",
  apps: [
    { name: "Validation Plan", description: "Create tests and measurable coverage targets.", href: "/apps/validation-plan" },
    { name: "Bench Setup", description: "Prepare instruments and connectivity.", href: "/apps/bench-setup" },
    { name: "Validation Insights", description: "Analyze results and recommend next actions.", href: "/apps/validation-insights" },
  ],
  agentGroups: [
    { name: "Planning", description: "Converts goals into tests and coverage." },
    { name: "Bench and execution", description: "Prepares and runs validation." },
    { name: "Insights", description: "Finds gaps, failures, and next actions." },
  ],
  reference: { title: "Product validation journey", description: "See planning, execution, and insight stay connected.", href: "/apps#reference-journeys", results: [{ label: "Plan", value: 100 }, { label: "Bench", value: 92 }, { label: "Run", value: 84 }, { label: "Learn", value: 96 }] },
});

export const loopOverviews: Record<string, LoopOverview> = {
  digital,
  "digital-implementation": implementation,
  fpga,
  analog,
  "mixed-signal": mixedSignal,
  firmware,
  validation,
};
