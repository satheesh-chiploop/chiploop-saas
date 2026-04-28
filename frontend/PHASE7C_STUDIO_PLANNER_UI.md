# Phase 7C Studio Planner UI

## Purpose

Phase 7C adds a structured Planner panel inside the existing Studio page at `/workflow`.
It uses the Phase 7A browser-safe backend endpoint to find existing agents and reusable
components before a user creates anything new.

Existing Studio canvas behavior, Planner modals, workflow execution, and saved workflow
flows are unchanged.

## UI Structure

Added component:

- `components/studio/PlannerPanel.tsx`

The panel is rendered in the existing right-side Studio area above the Runs list. It is
additive and does not replace:

- `PlannerModal`
- `AgentPlannerModal`
- ReactFlow canvas
- workflow run controls
- run history

## API Used

The panel calls:

```text
POST /api/studio/agent-planner/plan
```

It uses the shared frontend API helper:

- `lib/apiClient.ts`

The helper attaches the current Supabase session bearer token. The browser does not call
`/sdk/*`.

## Planner Input

Current inputs:

- Free text requirement/spec.
- Optional domain.
- Current Studio loop type from `/workflow`.

No workflow, registry, or generated-agent state is persisted by this UI.

## Planner Output

The panel displays:

- Exact Matches
- Similar Matches
- Reusable Components
  - skills
  - tools
  - hooks
- Missing Capabilities
- Recommendation
- Confidence
- Explanation

## Actions

Exact matches include a `Use` action. This adds the selected agent as a node on the current
ReactFlow canvas and, when possible, connects it after the rightmost existing node.

The `Generate Agent (dry-run)` action is intentionally a Phase 7D stub. It does not call
Agent Factory and does not generate files.

## Test Steps

Run:

```bash
npx eslint components/studio/PlannerPanel.tsx app/workflow/page.tsx
npm run build
```

Manual checks:

- `/workflow` loads.
- Existing Design Intent Planner modal still opens.
- Existing System Planner modal still opens.
- Existing canvas drag/drop still works.
- Existing workflow run controls still render.
- Planner panel renders in the right-side panel.
- Planner request calls `/api/studio/agent-planner/plan`.
- Exact match `Use` action adds a node to the canvas.
- `Generate Agent (dry-run)` shows the Phase 7D stub and does not generate files.

## Risks

- `app/workflow/page.tsx` is already large and has existing lint issues unrelated to this
  change.
- The right-side panel now shares vertical space between Planner and Runs.
- Planner results depend on the backend registry and Supabase session auth being available.

## Next Steps

Phase 7D should add Agent Factory dry-run review UI using:

```text
POST /api/studio/agent-factory/dry-run
```

That UI should remain dry-run only and should not promote generated files automatically.
