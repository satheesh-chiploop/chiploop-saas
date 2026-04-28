# Phase 7E DAG Preview UI

## Purpose

Phase 7E adds a DAG Preview modal to Studio. It lets users validate workflow graph
structure and inspect possible serial/parallel execution order without running agents.

## Endpoints Used

The browser calls:

```text
POST /api/studio/dag/preview
POST /api/studio/dag/validate
```

The UI uses the shared `lib/apiClient.ts` helper. It does not call `/sdk/*`.

## Safety Rules

- Preview only.
- Does not execute agents.
- Does not change default workflow execution mode.
- Does not save workflows.
- Does not modify registry or agent files.
- Existing App workflows are untouched.

## UI Behavior

Added component:

- `components/studio/DagPreviewModal.tsx`

Studio sidebar now includes `DAG Preview` near the existing planner buttons.

The modal supports:

- sample DAG payload
- current Studio canvas graph payload
- pasted workflow/DAG JSON
- Preview call
- Validate call

Displayed result sections:

- validation state
- nodes
- edges
- serial execution order
- parallel groups
- parallel group agents
- dependency graph
- dependency warnings
- validation errors

The result area scrolls independently inside the modal.

## Validation Steps

Run:

```bash
npx eslint components/studio/DagPreviewModal.tsx
npm run build
```

Manual checks:

- `/workflow` loads.
- Left sidebar remains tidy.
- `DAG Preview` opens a modal.
- `Use sample` then `Run Preview` returns a preview.
- `Validate` returns validation status/errors.
- `Use current Studio workflow` populates JSON from the canvas when nodes exist.
- Closing the modal returns to the original Studio layout.
- Existing workflow run controls still render and are unchanged.

## Next Step

Phase 7F should add generated-agent review UI for inspecting generated file plans and
registry patches before any manual promotion workflow is considered.
