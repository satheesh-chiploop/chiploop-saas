# Phase 7C Studio Planner UI

## Purpose

Phase 7C adds a structured Agent Planner modal inside the existing Studio page at `/workflow`.
It uses the Phase 7A browser-safe backend endpoint to find existing agents and reusable
components before a user creates anything new.

Existing Studio canvas behavior, Planner modals, workflow execution, and saved workflow
flows are unchanged.

## UI Structure

Added component:

- `components/studio/AgentPlannerModal.tsx`

The modal opens from an `Agent Planner` button in the left Studio sidebar, directly below
the existing `System Planner` button. It is additive and does not replace:

- `PlannerModal`
- `AgentPlannerModal`
- ReactFlow canvas
- workflow run controls
- run history

The modal content scrolls independently and does not affect the ReactFlow canvas layout.

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
- Planned agent name.
- Loop selector.
- Optional domain.

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

The Save action stores the current planner result in local modal state for the active
Studio session only. It does not call a backend save endpoint.

The `Generate Agent (dry-run)` action is intentionally a Phase 7D stub. It does not call
Agent Factory and does not generate files.

## Test Steps

Run:

```bash
npx eslint components/studio/AgentPlannerModal.tsx
npm run build
```

Manual checks:

- `/workflow` loads cleanly.
- Left sidebar remains tidy.
- Buttons appear in this order: `Design Intent Planner`, `System Planner`, `Agent Planner`.
- Existing Design Intent Planner modal still opens.
- Existing System Planner modal still opens.
- Existing canvas drag/drop still works.
- Existing workflow run controls still render.
- Agent Planner button opens a modal.
- Planner request calls `/api/studio/agent-planner/plan`.
- Result displays inside the modal.
- Closing the modal returns to the original Studio layout.
- `Generate Agent (dry-run)` shows the Phase 7D stub and does not generate files.

## Risks

- `app/workflow/page.tsx` is already large and has existing lint issues unrelated to this
  change.
- Agent Planner save state is local to the open modal session.
- Planner results depend on the backend registry and Supabase session auth being available.

## Next Steps

Phase 7D should add Agent Factory dry-run review UI using:

```text
POST /api/studio/agent-factory/dry-run
```

That UI should remain dry-run only and should not promote generated files automatically.
