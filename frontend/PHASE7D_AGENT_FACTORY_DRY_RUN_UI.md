# Phase 7D Agent Factory Dry-Run UI

## Purpose

Phase 7D adds a review-only Agent Factory dry-run modal in Studio. It lets users inspect
what the backend would generate for a new or extended agent without writing files,
promoting registry patches, or changing workflow execution.

## Endpoint Used

The browser calls:

```text
POST /api/studio/agent-factory/dry-run
```

The UI uses the shared `lib/apiClient.ts` helper, which sends the Supabase session bearer
token. The browser does not call `/sdk/*`.

## Safety Rules

- Always sends `dry_run: true`.
- Never sends `write: true`.
- Does not save generated files.
- Does not promote registry patches.
- Does not modify the Studio canvas.
- If the backend response includes written-file metadata, the UI shows a warning and does
  not use those outputs.

## UI Behavior

The existing Agent Planner modal now shows `Generate Agent Dry Run` only when the planner
recommendation is one of:

- `create_new`
- `extend_existing`
- `extend_or_create_variant`

The dry-run modal is prefilled from the planner:

- agent name
- natural language request
- loop type
- domain
- reusable skills/tools/hooks
- missing capabilities as desired outputs

Editable fields:

- agent name
- description/request
- loop
- domain

Result sections:

- decision
- proposed AgentSpec
- proposed Skills
- proposed Tools
- proposed Hooks
- generated file plan
- registry patch plan
- validation checklist
- risks

Copy buttons:

- AgentSpec JSON
- Registry patch content when present

## Validation Steps

Run:

```bash
npx eslint components/studio/AgentPlannerModal.tsx components/studio/AgentFactoryDryRunModal.tsx
npm run build
```

Manual checks:

- `/workflow` loads.
- `Agent Planner` opens from the left sidebar.
- Planner result still displays.
- `Generate Agent Dry Run` appears only for create/extend recommendations.
- Dry-run modal opens without disturbing the canvas or sidebar.
- Dry-run API call returns readable, scrollable results.
- Copy buttons work for AgentSpec and registry patch content.
- Closing the dry-run modal returns to the planner modal.
- Closing planner returns to the original Studio layout.

## Next Step

Phase 7E should add generated-agent review UI for comparing generated file plans and
registry patches before any manual promotion workflow is considered.
