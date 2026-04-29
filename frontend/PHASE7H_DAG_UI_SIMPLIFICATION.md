# Phase 7H DAG UI Simplification

Date: 2026-04-28

## Purpose

The previous DAG Preview modal exposed workflow JSON, DAG nodes, edges, dependency graph, and parallel groups by default. This update keeps the same backend preview/validate APIs but changes the frontend experience into a simpler Optimize Workflow flow.

## Routes And Components

Updated:

- `frontend/app/workflow/page.tsx`
- `frontend/components/studio/DagPreviewModal.tsx`

The Studio sidebar button is now labeled `Optimize Workflow`.

## UI Behavior

Default Simple Mode:

- Choose workflow source:
  - Current workflow
  - Saved workflow
- Choose a saved workflow from the dropdown when using saved workflow mode.
- Click `Analyze Parallelism`.
- See readable result cards:
  - Validation status
  - Estimated benefit
  - Parallel group count
  - Current serial steps
  - Recommended parallel groups
  - Warnings

Advanced Mode:

- Collapsed by default.
- Contains workflow JSON editor.
- Contains raw nodes, edges, parallel groups, and dependency graph.
- Keeps the existing preview and validate calls for technical review.

## Safety Rules

- The UI still calls only:
  - `POST /api/studio/dag/preview`
  - `POST /api/studio/dag/validate`
- The UI does not execute workflows.
- The UI does not enable DAG execution.
- The UI does not modify workflow execution behavior.
- Raw DAG JSON is hidden by default.

## Save Buttons

The UI includes:

- `Save as Copy`
- `Save to Same Workflow`

Because no backend DAG save endpoint exists yet and backend changes were out of scope, these buttons do not write data. They explain that DAG save support is not enabled yet.

## Manual Test Steps

1. Open `/workflow`.
2. Confirm the left panel shows `Optimize Workflow`.
3. Click `Optimize Workflow`.
4. Confirm JSON is not shown by default.
5. Select `Current workflow`.
6. Click `Analyze Parallelism`.
7. Confirm readable serial steps and parallel groups appear.
8. Expand `Advanced JSON and Dependency Details`.
9. Confirm raw JSON and dependency details are available only there.
10. Confirm no workflow executes.

## Known Limitations

- Saved workflow analysis uses existing Supabase workflow definitions from the browser.
- Save as Copy and Save to Same Workflow are non-writing placeholders until backend DAG save endpoints are added.
- Estimated benefit is stage-count based, not runtime-duration based.
