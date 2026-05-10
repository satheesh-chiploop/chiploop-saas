# ChipLoop Demo Slides

## Slide 1: ChipLoop
Agentic AI workflows for chip design execution and inspection.

- Turn design intent into structured workflows
- Run Apps like Arch2RTL
- Inspect outputs with Ask This Run
- Extend workflows in Studio

## Slide 2: Why This Matters
Prompt-only AI is not enough for chip design.

- Chip work needs traceable inputs, outputs, and artifacts
- Engineers need repeatable workflows, not one-off answers
- Reviews need logs, reports, RTL, constraints, and handoff packages
- Teams need execution plus inspection

## Slide 3: What ChipLoop Provides
ChipLoop pairs execution with AI-assisted inspection.

- Apps for guided workflows
- Studio for custom agent workflows
- Ask This Run for report and log inspection
- GitHub, CLI, SDK, Cursor, and VS Code paths for developer workflows

## Slide 4: Demo Flow
Today we will follow one connected path.

1. Start from Apps
2. Run Arch2RTL with a PWM controller
3. Review generated outputs
4. Ask This Run questions
5. Open Studio and explain workflow building blocks
6. Show GitHub and developer integrations
7. Close with next steps

## Slide 5: Start With Apps
Apps are the guided entry point.

- Open Home -> Apps
- Choose Arch2RTL
- Use a prepared PWM controller spec
- Click Run Arch2RTL

## Slide 6: Demo Spec
PWM controller requirement.

```text
Design a parameterized PWM controller.

Inputs:
- clk
- reset_n
- enable
- duty_cycle[7:0]
- period[7:0]

Outputs:
- pwm_out
- counter_value[7:0]
```

## Slide 7: What The Run Produces
Arch2RTL creates reviewable engineering artifacts.

- RTL-oriented design output
- Constraints and handoff files
- Logs and run metadata
- Downloadable artifacts
- Inspection context for Ask This Run

## Slide 8: Ask This Run
Inspection turns generated files into answers.

Ask questions like:

- What was generated?
- Summarize the RTL handoff.
- What should I verify in simulation?
- Are any reset or interface assumptions missing?

## Slide 9: Studio
Studio is the advanced workflow workspace.

- Workflows connect agents
- Agents perform scoped engineering tasks
- Design intent captures requirements and assumptions
- Workflow Composer inspects saved workflows and analyzes parallel stages before execution

## Slide 10: Agent Planner
Agent Planner creates private agents from requirements.

- Go to Home -> Studio -> Agent Planner
- Choose create new private agent
- Define goal, inputs, outputs, skill, MCP/tool, and hooks
- Review, edit, and save the agent

## Slide 11: System Planner And Design Intent
System-level work needs structure before execution.

- System Planner turns broad goals into multi-agent workflows
- Design Intent Analyzer extracts constraints and assumptions
- Design Intent Library stores reusable engineering intent
- Workflows become easier to rerun and inspect

## Slide 12: GitHub Integration
Users bring repository context into ChipLoop.

- Each user connects their own GitHub account
- User selects allowed repositories
- Apps and Studio can import selected files
- Admin does not manage each user connection

## Slide 13: Developer Workflows
ChipLoop fits into engineering tools.

- API keys for SDK and CLI
- Cursor via integrated terminal
- VS Code via CLI-backed workflow
- GitHub Actions for automation

## Slide 14: Closing Message
ChipLoop is not just prompt-based generation.

- It executes structured chip workflows
- It produces reviewable artifacts
- It helps inspect logs, reports, and outputs
- It gives students, engineers, and teams a workflow system they can build on

## Slide 15: Call To Action
Recommended next step.

- Try the Arch2RTL demo
- Use Ask This Run after completion
- Join the weekly demo or workshop
- Connect GitHub when ready to use your own repository context
