# ChipLoop Demo Speaker Script

## Slide 1: ChipLoop
Welcome everyone. Today I will show ChipLoop, an agentic AI platform for chip design workflows. The key idea is simple: we do not want AI to stop at a prompt response. We want AI to help execute structured chip design workflows, produce artifacts, and then help inspect what happened.

## Slide 2: Why This Matters
In chip design, prompt-only AI is not enough. Engineers need traceable inputs and outputs. They need logs, generated files, reports, constraints, RTL, and review points. ChipLoop is built around that reality. It pairs generation with workflow structure and inspection.

## Slide 3: What ChipLoop Provides
ChipLoop has a few main surfaces. Apps are guided workflows for common flows like Arch2RTL. Studio is where advanced users build and modify agent workflows. Ask This Run lets users ask questions about completed runs using the logs and artifacts. For developers, ChipLoop also supports GitHub, CLI, SDK, Cursor, and VS Code workflows.

## Slide 4: Demo Flow
Here is the sequence I will follow. I will start in Apps, run Arch2RTL using a PWM controller requirement, review the generated outputs, then use Ask This Run. After that I will show how Studio expands this into custom workflows, and I will close with GitHub and developer integration paths.

## Slide 5: Start With Apps
I am starting with Apps because it is the easiest entry point for a new user. From Home, I open Apps and choose Arch2RTL. This is the guided flow for turning an architecture-style requirement into RTL-oriented handoff artifacts. For the demo, I will use a prepared PWM controller spec.

## Slide 6: Demo Spec
This is the requirement we will use. It defines a parameterized PWM controller with clock, reset, enable, duty cycle, period, PWM output, and counter output. This kind of structured input is important because the workflow has enough information to generate useful artifacts and also enough context for later inspection.

## Slide 7: What The Run Produces
Once I click Run Arch2RTL, ChipLoop executes the workflow. The important point is that the result is not just text on a page. The run produces engineering artifacts, logs, metadata, and files that can be downloaded and reviewed. These artifacts become the basis for inspection and iteration.

## Slide 8: Ask This Run
After the run finishes, I use Ask This Run. This is where ChipLoop pairs execution with inspection. Instead of manually opening every log and generated file, I can ask questions like: What was generated? Summarize the RTL handoff. What should I verify in simulation? Are any reset assumptions missing? This makes the result easier to review.

## Slide 9: Studio
Now I will switch to Studio. Studio is the advanced workspace. The key concepts are workflows, agents, and design intent. A workflow connects agents into an execution path. Agents do scoped engineering tasks. Design intent captures requirements, constraints, and assumptions so future runs are more consistent.

## Slide 10: Agent Planner
Agent Planner is used when a workflow needs a new private agent. The user goes to Home, Studio, Agent Planner. They can choose to create a new private agent, define the goal, inputs, outputs, one skill, one MCP or tool connection, and any hooks. Then they review and save the agent before using it in workflows.

## Slide 11: System Planner And Design Intent
For broader goals, System Planner helps turn a system-level objective into a multi-agent workflow. Design Intent Analyzer extracts constraints, assumptions, interfaces, and verification intent from specs or repository context. The Design Intent Library keeps reusable intent so teams do not repeat the same assumptions in every workflow.

## Slide 12: GitHub Integration
GitHub is user-driven. Each user connects their own GitHub account and selects which repositories ChipLoop can access. After that, Apps and Studio can import selected files as context. The administrator configures the GitHub App once, but does not need to manage each user connection.

## Slide 13: Developer Workflows
For developers, ChipLoop also supports API-key based workflows. Users can create an API key and use the SDK or CLI. Cursor works through the integrated terminal. VS Code follows the same CLI-backed path. GitHub Actions can use the CLI for automation. This means ChipLoop can fit into a normal engineering workflow, not only a browser demo.

## Slide 14: Closing Message
The main message is that ChipLoop is not just prompt-based generation. It is a workflow system. It executes structured chip design flows, produces reviewable artifacts, and helps inspect the result. That is useful for students learning workflows, engineers building faster, and teams trying to make AI output more reviewable.

## Slide 15: Call To Action
The recommended next step is to try the Arch2RTL demo, wait for the run to finish, and use Ask This Run. After that, users can connect GitHub when they are ready to use their own repository context. For deeper learning, they can join the weekly demo or the paid workshop.
