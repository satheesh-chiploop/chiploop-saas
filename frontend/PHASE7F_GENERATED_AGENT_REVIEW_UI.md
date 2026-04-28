# Phase 7F Generated Agent Review UI

## Purpose

Phase 7F adds a review-only Generated Agents modal inside Studio. It lets users inspect
the latest Agent Factory dry-run output from the current UI session without saving files,
modifying registry metadata, or promoting generated agents.

## Data Source

No backend generated-agent list endpoint is used in this phase. The modal reviews the
latest dry-run result produced by:

```text
POST /api/studio/agent-factory/dry-run
```

The browser does not call `/sdk/*`.

## Safety Rules

- No backend changes.
- No registry modification.
- No generated file writes.
- No patch merge or promotion actions.
- No approve button.
- No production workflow behavior changes.

## UI Behavior

Added component:

- `components/studio/GeneratedAgentReviewModal.tsx`

Studio sidebar now includes:

- `Generated Agents`

The review modal displays:

- generated agent name
- Manual Review Required status
- proposed AgentSpec
- generated files list
- registry patch YAML
- validation checklist
- risks
- migration notes

Copy actions:

- AgentSpec JSON
- registry patch YAML
- generated file content previews when available

If no dry-run exists in the current Studio session, the modal shows an empty state and
instructs the user to run Agent Planner and Agent Factory Dry Run first.

## Validation Steps

Run:

```bash
npx eslint components/studio/GeneratedAgentReviewModal.tsx components/studio/AgentFactoryDryRunModal.tsx components/studio/AgentPlannerModal.tsx
npm run build
```

Manual checks:

- `/workflow` loads.
- `Generated Agents` opens a modal.
- Empty state appears before any dry-run.
- Agent Planner still opens.
- Agent Factory dry-run still works.
- After dry-run, Generated Agents modal shows the latest dry-run result.
- Copy buttons work.
- No approve, merge, write, save-generated, or registry promotion action exists.
- Existing Apps and Studio canvas are unaffected.

## Next Step

Future work can add a backend generated-agent listing endpoint and governance workflow.
Until then, promotion remains a manual developer process outside the browser UI.
