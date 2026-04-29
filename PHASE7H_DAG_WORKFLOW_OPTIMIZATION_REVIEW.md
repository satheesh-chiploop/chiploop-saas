# Phase 7H DAG Workflow Optimization Review

Date: 2026-04-28

## Scope

This is a review-only strategy document for simplifying the DAG Preview experience and turning it into a production-quality workflow parallelization UX.

No frontend or backend behavior was changed.

## Current DAG Flow

The current frontend DAG UI is implemented in:

- `frontend/components/studio/DagPreviewModal.tsx`
- Mounted from `frontend/app/workflow/page.tsx`

The Studio left panel currently has a `DAG Preview` button near:

- Design Intent Planner
- System Planner
- Agent Planner
- Generated Agents

Clicking `DAG Preview` opens a modal with:

- A workflow JSON textarea.
- `Use current Studio workflow`.
- `Use sample`.
- `Run Preview`.
- `Validate`.
- Raw result sections for nodes, edges, serial execution order, parallel groups, parallel group agents, dependency graph, warnings, and errors.

This is technically useful, but it is an expert/debugging interface rather than a user-facing optimization flow.

## How Use Current Studio Workflow Works

`DagPreviewModal` receives the current ReactFlow `nodes` and `edges` from `frontend/app/workflow/page.tsx`.

`Use current Studio workflow` converts the canvas into this payload shape:

```json
{
  "graph": {
    "nodes": [
      {
        "id": "node-id",
        "data": {
          "uiLabel": "Digital RTL Agent",
          "backendLabel": "Digital RTL Agent"
        }
      }
    ],
    "edges": [
      {
        "source": "source-node-id",
        "target": "target-node-id"
      }
    ]
  },
  "loop_type": "digital"
}
```

The modal then posts that payload to:

- `POST /api/studio/dag/preview`
- `POST /api/studio/dag/validate`

Because browser routes use `/api/*` rewrites, these map to backend:

- `POST /studio/dag/preview`
- `POST /studio/dag/validate`

## Backend Endpoint Map

The browser-safe DAG endpoints are in `backend/browser_routes.py`.

`POST /studio/dag/preview`:

- Requires browser session auth.
- Accepts one of:
  - `{ "dag": { ... } }`
  - `{ "graph": { nodes, edges }, "loop_type": "..." }`
  - `{ "agents": [...], "loop_type": "...", "infer_parallel": true }`
  - a raw `WorkflowDAG` shape.
- Converts payload with `_dag_from_payload`.
- Validates with `workflow_dag.validator.validate_dag`.
- Produces a dry-run preview with `workflow_dag.planner.dry_run_plan`.
- Does not execute agents.

`POST /studio/dag/validate`:

- Requires browser session auth.
- Converts payload the same way.
- Validates the DAG.
- Does not execute agents.

Current response shape includes:

```json
{
  "status": "ok",
  "valid": true,
  "warnings": [],
  "errors": [],
  "dag": {
    "workflow_mode": "dag",
    "nodes": [],
    "edges": [],
    "metadata": {}
  },
  "preview": {
    "workflow_mode": "dag",
    "dry_run": true,
    "execution_order": [],
    "parallel_groups": [],
    "dependency_graph": {},
    "parallel_group_agents": []
  }
}
```

## Backend DAG Module

The DAG implementation lives in `backend/workflow_dag/`.

Key files:

- `models.py`
- `planner.py`
- `validator.py`
- `executor.py`
- `state_store.py`
- `examples.py`

Current capabilities:

- `WorkflowDAG`, `DAGNode`, `DAGEdge`, execution state/result models.
- Convert agent lists to DAGs with `dag_from_agents`.
- Convert Studio canvas graphs to DAGs with `dag_from_studio_graph`.
- Infer simple parallelization from agent names when `infer_parallel=True`.
- Dry-run topological execution with `dry_run_plan`.
- Validate cycles, missing dependencies, missing registry agents, orphan nodes, and required input satisfaction.
- Execute opt-in DAGs through `execute_dag`, using `ThreadPoolExecutor` and existing Agent Runtime wrappers.

Important safety point:

- The current browser DAG endpoints only preview and validate. They do not execute DAGs.

## Automatic DAG Conversion Status

Current automatic conversion is partial:

- Agent-list input can infer simple parallel groups with name-based heuristics in `_infer_dependencies`.
- Current Studio graph input preserves the existing graph edges and computes topological groups.
- The current graph conversion does not deeply infer data dependencies from agent inputs/outputs, artifacts, or registry metadata.

This is good enough for preview, but not enough to silently rewrite production workflows.

## Workflow Storage Analysis

Workflow persistence is currently centered on the Supabase `workflows` table.

Relevant backend functions:

- `backend/main.py` `_load_workflow_def_by_name`
- `backend/main.py` `_toposort_nodes`
- `backend/main.py` `_definition_to_executor_nodes`
- `backend/main.py` `save_custom_workflow`

Current saved workflow shape:

```json
{
  "user_id": "uuid-or-null",
  "name": "Workflow Name",
  "goal": "",
  "summary": "",
  "loop_type": "digital",
  "definitions": {
    "nodes": [],
    "edges": []
  },
  "status": "saved"
}
```

Workflow loading:

- User-owned custom workflows are loaded by exact name and `user_id`.
- Global prebuilt workflows are loaded with `is_prebuilt = true`.
- Definitions are unpacked from `definitions.nodes` and `definitions.edges`, with fallbacks to top-level `nodes` and `edges`.

Workflow execution:

- Current default execution converts saved definitions into a serial executor node list.
- `_toposort_nodes` uses edges only to order nodes.
- There is no indication that DAG mode is currently used by the normal App or Studio run path.

Current save behavior caveat:

- Some frontend save paths send a flat payload with `name`, `definitions`, and `loop_type`.
- `save_custom_workflow` primarily reads nested `data.workflow`.
- This is separate from DAG UX, but it should be cleaned up before adding save-as-DAG APIs.

Can workflow metadata store DAG data?

- Yes, the existing `definitions` JSON can store additional fields without changing serial behavior if the runner continues reading `definitions.nodes` and `definitions.edges`.
- Recommended shape:

```json
{
  "nodes": [],
  "edges": [],
  "workflow_mode": "serial",
  "dag": {
    "workflow_mode": "dag",
    "nodes": [],
    "edges": [],
    "metadata": {
      "opt_in": true,
      "created_by": "dag_optimizer_v1"
    }
  },
  "dag_preview": {
    "parallel_groups": [],
    "execution_order": []
  }
}
```

Default behavior should remain:

- `workflow_mode = "serial"` unless the user explicitly enables DAG execution.
- Serial runner ignores `definitions.dag` unless a future opt-in execution path is selected.

## Current UX Problems

1. JSON is the primary interface.

   Most users should not need to paste or understand DAG JSON to optimize a workflow.

2. The result sections are implementation-level.

   Raw nodes, edges, dependency graph, and parallel group ids expose internals instead of explaining what will happen.

3. There is no simple "optimize this workflow" path.

   Users need to know whether to use current workflow, sample JSON, preview, or validate.

4. There is no saved workflow selector.

   The most natural action is to select a saved workflow and ask ChipLoop to analyze it.

5. There is no save behavior.

   Users can preview but cannot accept suggestions, save a copy, or update the workflow.

6. Simple and advanced modes are mixed.

   JSON editing, validation, and dependency internals are shown by default.

7. Benefit and risk are not explained.

   Users need to see what can run together, what must stay serial, and why.

8. No distinction between preview and execution mode.

   The modal says preview-only, but it does not clearly connect saving DAG metadata with future opt-in DAG execution.

## Recommended Simplified DAG UX

Rename the user-facing entry from `DAG Preview` to:

- `Optimize Workflow`

or:

- `Parallelize Workflow`

### Simple Mode

Simple Mode should be the default.

Flow:

1. User opens `Optimize Workflow`.
2. User selects:
   - Current Studio workflow, or
   - Saved workflow from a dropdown.
3. User clicks `Analyze Parallelism`.
4. ChipLoop shows a readable summary.
5. User accepts suggestions.
6. User saves:
   - Save as Copy
   - Save to Same Workflow
7. DAG remains opt-in. Existing serial execution remains default unless user later chooses DAG execution.

Simple Mode fields:

- Workflow source:
  - Current canvas
  - Saved workflow
- Workflow name.
- Loop type.
- Number of agents.
- Current serial order.

Analyze result should show:

- Current serial order:
  - Step 1: Spec Agent
  - Step 2: RTL Agent
  - Step 3: Testbench Agent
  - Step 4: Firmware Prep Agent

- Recommended parallel groups:
  - Group 1: Spec Agent
  - Group 2: RTL Agent
  - Group 3: Testbench Agent, Firmware Prep Agent, Software Prep Agent
  - Group 4: Integration Agent

- Estimated benefit:
  - "Potentially reduces workflow stages from 6 to 4."
  - "2 groups can run in parallel."

- Risk warnings:
  - "Simulation depends on RTL artifacts and cannot start before RTL generation."
  - "Firmware and software preparation appear independent after register map generation."
  - "This is a preview. DAG execution is not enabled automatically."

Buttons:

- `Analyze Parallelism`
- `Save as Copy`
- `Save to Same Workflow`
- `Advanced Edit`
- `Close`

Save labels should be explicit:

- `Save as Copy`
  - Creates a new workflow with DAG metadata.
  - Recommended default.

- `Save to Same Workflow`
  - Updates the current workflow metadata.
  - Should require confirmation.

### Advanced Mode

Advanced Mode should be collapsed by default.

Advanced Mode can include:

- JSON editor.
- Raw nodes.
- Raw edges.
- Dependency graph.
- Manual dependency editing.
- Validation errors.
- Future drag-and-drop dependency graph editor.

Advanced mode should be labeled:

- `Advanced: DAG JSON and Dependencies`

This keeps power-user features without making the common path feel technical.

## Recommended Backend Changes

Add browser-safe, session-authenticated endpoints:

### `POST /studio/workflows/{workflow_id}/parallelism/analyze`

Purpose:

- Analyze an existing workflow by id.
- Return a user-friendly optimization summary.
- Do not execute agents.
- Do not save anything.

Input:

```json
{
  "source": "saved_workflow",
  "infer_parallel": true
}
```

Output:

```json
{
  "status": "ok",
  "workflow_id": "uuid",
  "workflow_name": "Arch2RTL",
  "workflow_mode": "serial",
  "current_serial_order": [
    { "node_id": "n1", "agent_name": "Digital Spec Agent" }
  ],
  "recommended_parallel_groups": [
    {
      "group": 1,
      "agents": ["Digital Spec Agent"],
      "reason": "Workflow entry point"
    }
  ],
  "estimated_benefit": {
    "serial_stages": 6,
    "parallel_stages": 4,
    "parallelizable_groups": 2
  },
  "warnings": [],
  "dag": {}
}
```

### `POST /studio/workflows/parallelism/analyze-current`

Purpose:

- Analyze current canvas graph without requiring it to be saved first.
- Accepts `{ nodes, edges, loop_type }`.
- Returns same summary shape as saved workflow analyze.

### `POST /studio/workflows/{workflow_id}/dag/save`

Purpose:

- Save accepted DAG metadata for an existing workflow.
- Does not enable DAG execution by default unless explicitly requested.

Input:

```json
{
  "dag": {},
  "dag_preview": {},
  "execution_default": "serial",
  "save_mode": "overwrite"
}
```

Rules:

- User must own workflow.
- Preserve `definitions.nodes` and `definitions.edges`.
- Store DAG metadata under `definitions.dag` and `definitions.dag_preview`.
- Keep `definitions.workflow_mode = "serial"` unless the user explicitly opts into DAG execution.

### `POST /studio/workflows/{workflow_id}/dag/save-copy`

Purpose:

- Create a copy of a workflow with DAG metadata.
- Recommended save path.

Input:

```json
{
  "new_name": "Arch2RTL Optimized",
  "dag": {},
  "dag_preview": {},
  "execution_default": "serial"
}
```

Rules:

- New workflow belongs to current user.
- New workflow status is `saved`.
- Copy keeps original serial graph and adds DAG metadata.

### Optional future endpoint

`POST /studio/workflows/{workflow_id}/dag/enable`

Purpose:

- Explicitly opt a saved workflow into DAG execution later.
- Should not be part of the first UX if DAG executor is not wired into normal runs.

## Recommended Frontend Changes

Replace the current default modal layout with a simpler two-mode UI.

Suggested component:

- Continue using `frontend/components/studio/DagPreviewModal.tsx`, but make it Simple Mode first.
- Or rename to `WorkflowOptimizationModal.tsx` later.

Simple Mode UI:

- Title: `Optimize Workflow`
- Subtitle: `Find safe parallel steps before changing execution.`
- Workflow source selector:
  - Current Studio workflow
  - Saved workflow
- Saved workflow dropdown using current `customWorkflows`.
- `Analyze Parallelism` button.
- Summary cards:
  - Current Serial Order
  - Recommended Parallel Groups
  - Estimated Benefit
  - Risk Warnings
- Actions:
  - Save as Copy
  - Save to Same Workflow
  - Advanced Edit
  - Close

Advanced Mode UI:

- Collapsed by default.
- JSON editor.
- Raw DAG nodes/edges.
- Dependency graph.
- Validation details.
- Manual dependency editing later.

Do not show by default:

- Raw DAG JSON.
- Raw node ids.
- Raw edge ids.
- Full dependency graph.

Still keep:

- Preview-only warning.
- Clear "DAG execution remains opt-in" note.
- Validation status.

## Save Behavior Recommendation

Default action should be `Save as Copy`.

Why:

- It avoids changing the user's existing known-good serial workflow.
- It creates a reviewable optimized variant.
- It supports side-by-side testing later.

Save to Same Workflow:

- Should be allowed for power users.
- Requires confirmation.
- Should preserve serial mode as default.

Recommended copy naming:

- `<Original Name> - Optimized`
- If name exists, append date or numeric suffix.

## Drag-And-Drop Recommendation

Drag-and-drop DAG editing is not needed for MVP.

MVP should be:

- Analyze existing workflow.
- Show suggested parallel groups.
- Let user save as copy or save to same workflow.
- Keep advanced JSON collapsed.

Drag-and-drop should come later after:

- DAG save metadata is stable.
- DAG execution opt-in path is stable.
- Dependency validation messages are user-friendly.
- There is a clear mental model for "runs after" dependencies.

Future drag-and-drop model:

- Visual lanes for parallel groups.
- Move an agent between stages.
- Draw or remove "depends on" links.
- Validate after each edit.
- Warn if moving a node violates artifact/data dependency.

Do not start with drag-and-drop because it increases implementation scope and can make unsafe dependency edits look easier than they are.

## Implementation Order

1. Add backend workflow parallelism analyze endpoint for saved workflow ids.
2. Add backend analyze-current endpoint for current canvas graphs.
3. Add backend save-copy endpoint for DAG metadata.
4. Add backend save-overwrite endpoint for DAG metadata with ownership checks.
5. Update frontend modal to Simple Mode by default.
6. Add saved workflow selector.
7. Add Analyze Parallelism button and readable result cards.
8. Add Save as Copy.
9. Add Save to Same Workflow with confirmation.
10. Move existing JSON editor/results into collapsed Advanced Mode.
11. Add tests for ownership, no execution, save-copy metadata shape, and serial default preservation.
12. Later: add DAG execution opt-in and manual dependency editor.

## Risks

1. Incorrect parallelization can break workflows.

   Mitigation: preview only, save as copy by default, serial execution remains default.

2. Name-based dependency inference is limited.

   Mitigation: show confidence/risk warnings and improve inference later using registry inputs/outputs/artifact metadata.

3. Existing save workflow paths are inconsistent.

   Mitigation: normalize save payload handling before adding DAG save endpoints.

4. Users may assume saved DAG metadata changes execution immediately.

   Mitigation: label the feature as optimization preview and explicitly state execution remains serial until enabled.

5. Advanced JSON can still overwhelm users.

   Mitigation: collapse advanced mode and make Simple Mode the default.

6. Workflow ownership must be enforced.

   Mitigation: all save/analyze endpoints for saved workflows should use session auth and verify `workflows.user_id`.

7. Raw filesystem or registry internals should not leak.

   Mitigation: return agent names, stage names, and warnings rather than raw paths or registry YAML.

## Summary Recommendation

The current DAG Preview should evolve from a technical JSON validator into an `Optimize Workflow` experience. The main user path should be: select current or saved workflow, analyze parallelism, review safe parallel groups, then save as a copy or update the same workflow. JSON editing and raw DAG details should move into collapsed Advanced Mode. Backend support should add workflow-aware analyze and save endpoints that store DAG metadata without changing default serial execution or executing agents.
