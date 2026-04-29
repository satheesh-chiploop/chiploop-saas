# Phase 7G Select And Generate Missing Agents Review

Date: 2026-04-28

## Scope

This is a review-only strategy document for the current System Planner flow and its overlap with the newer Studio Agent Planner and Agent Factory.

No frontend or backend behavior was changed.

## Current Frontend Entry Points

The Studio canvas lives in `frontend/app/workflow/page.tsx`.

The relevant buttons in the left panel are:

- Design Intent Planner: opens `frontend/components/PlannerModal.tsx`.
- System Planner: opens `frontend/components/AgentPlannerModal.tsx`.
- Agent Planner: opens the newer Studio Agent Planner modal.
- DAG Preview and Generated Agents are newer review-only Studio additions.

The legacy System Planner flow is primarily implemented in `frontend/components/AgentPlannerModal.tsx`, despite the component name overlapping with the newer Studio Agent Planner.

Related frontend files:

- `frontend/components/AgentPlannerModal.tsx`
- `frontend/components/PlannerModal.tsx`
- `frontend/components/MissingAgentNamingDialog.tsx`
- `frontend/app/workflow/page.tsx`
- `frontend/app/workflow/AgentNode.tsx`
- `frontend/components/studio/AgentPlannerModal.tsx`
- `frontend/components/studio/AgentFactoryDryRunModal.tsx`
- `frontend/components/studio/GeneratedAgentReviewModal.tsx`

## Current Backend Endpoint Map

System Planner endpoints currently used by frontend:

- `POST /analyze_spec`
- `POST /plan_workflow`
- `POST /generate_missing_agents_batch`
- `POST /build_workflow`
- `POST /save_custom_workflow`
- `POST /auto_compose_workflow`

Related custom-agent endpoints:

- `POST /save_custom_agent`
- `DELETE /delete_custom_agent`
- `POST /rename_custom_agent`
- `POST /publish_custom_agent`
- `GET /agents/get_code`
- `POST /agents/save_code`

Observed stale or risky references:

- `POST /suggest_next_agent` is called from `frontend/app/workflow/page.tsx` and `frontend/app/workflow/AgentNode.tsx`, but no active backend route was found in `backend/main.py` during this review.

Newer Studio endpoints from Phase 7A:

- `POST /studio/agent-planner/plan`
- `POST /studio/agent-factory/dry-run`
- `POST /studio/dag/preview`
- `POST /studio/dag/validate`
- `GET /studio/registry/summary`

## Current Select Agents Flow

The Select Agents button in `frontend/components/AgentPlannerModal.tsx` calls `handleSelectAgents`.

Input:

- User-entered `goal`.
- Optional `structured_spec_final` from `Analyze Spec`.
- Supabase session user id, falling back to `anonymous`.

Request shape:

```json
{
  "prompt": "user goal text",
  "structured_spec_final": {},
  "user_id": "supabase-user-id-or-anonymous"
}
```

Backend route:

- `POST /plan_workflow`
- Implemented in `backend/main.py`.
- Delegates to `planner.ai_work_planner.plan_workflow`.

Backend behavior:

- If no structured spec is provided, `plan_workflow` calls `/analyze_spec` internally with `user_id: "anonymous"`.
- It loads platform capabilities from `agent_capabilities.AGENT_CAPABILITIES`.
- It computes deterministic candidate agents through `planner.capability_graph.get_candidate_agents`.
- It attempts user-scoped semantic reuse through the Supabase RPC `match_agents_user` when a real user id is available.
- It asks the LLM to return a JSON plan using only existing agent names.
- It calculates `missing_agents` by comparing suggested names against `AGENT_CAPABILITIES`.
- It may add deterministic required agents from `agents.agent_selector.select_required_agents`.
- It may add a behavioral/control missing agent using `llm_detect_missing_behavioral_agents`.

Response shape expected by frontend:

```json
{
  "status": "ok",
  "plan": {
    "loop_type": "digital",
    "agents": ["Digital Spec Agent", "Digital RTL Agent"],
    "missing_agents": ["Digital Controller Agent"]
  }
}
```

Frontend state updated:

- `preplan = plan`
- `selectedAgents = plan.agents`
- `missingAgents = plan.missing_agents`
- `finalAgents = plan.agents`

Current source of available agents:

- Main selection is driven by backend `AGENT_CAPABILITIES`.
- Semantic reuse can include user-scoped Supabase matches through `match_agents_user`.
- The canvas sidebar separately loads custom agents directly from Supabase `agents` where `owner_id = current user`.
- The selection path does not appear to merge a structured list of `global agents + current user's private agents` before LLM planning. It relies on `AGENT_CAPABILITIES` plus semantic matches.

## Current Generate Missing Agents Flow

The Generate Missing Agent button in `frontend/components/AgentPlannerModal.tsx` calls `handleGenerateMissingAgents`.

If Select Agents was not run yet and a structured spec exists, the frontend calls `/plan_workflow` again to find missing agents. This fallback does not include `user_id`, so user-scoped reuse can be skipped in that branch.

Then `MissingAgentNamingDialog` opens.

`frontend/components/MissingAgentNamingDialog.tsx`:

- Receives missing agent names.
- Prefixes each with the detected domain.
- Ensures an `Agent` suffix.
- Lets the user rename generated agents.
- Communicates that agents will be added to the Custom Agents library.

On confirm, frontend calls:

```json
{
  "goal": "user goal text",
  "user_id": "supabase-user-id",
  "agent_names": ["Digital Controller Agent"],
  "structured_spec_final": {}
}
```

Backend route:

- `POST /generate_missing_agents_batch`
- Implemented in `backend/main.py`.
- Delegates to `planner.ai_agent_planner.generate_missing_agents_batch`.

Backend generation behavior:

- Infers `loop_type` from `structured_spec_final.loop_type`, defaulting to `digital`.
- Calls `agents.agent_generator.generate_behavioral_agent(name, loop_type)`.
- `generate_behavioral_agent` writes a Python file into `backend/agents/<loop_type>/<agent_name>.py`.
- Upserts the agent into Supabase `agents` with:
  - `agent_name`
  - `loop_type`
  - `script_path`
  - `description`
  - `is_custom = true`
  - `owner_id = user_id`
  - `is_prebuilt = false`
- Upserts `agent_memory` with `user_id`, capability tags, and capability embedding.

Response shape expected by frontend:

```json
{
  "status": "ok",
  "created_agents": [
    {
      "agent_name": "Digital Controller Agent",
      "loop_type": "digital",
      "path": "backend/agents/digital/digital_controller_agent.py",
      "description": "Behavioral agent auto-derived for Digital Controller Agent"
    }
  ],
  "loop_type": "digital"
}
```

Frontend after generation:

- Appends generated agents to `localStorage.custom_agents`.
- Dispatches `refreshAgents`.
- Reloads custom agents from Supabase `agents.owner_id`.
- Appends newly generated agent names to the end of the final agent list.
- Clears `missingAgents`.
- Enables Build Workflow.

Current save/scoping behavior:

- Generated missing agents are saved to Supabase with `owner_id = user_id`.
- Generated code is written into shared backend source directories under `backend/agents/<loop_type>/`.
- The frontend also stores generated agents in `localStorage.custom_agents`.
- `POST /save_custom_agent` inserts into Supabase `agents` but does not set `owner_id`, which is inconsistent with the generate-missing path.
- `DELETE /delete_custom_agent` scopes by `owner_id`.
- `POST /rename_custom_agent` scopes by `user_id`, not `owner_id`, which is inconsistent with delete/load/publish.
- `POST /publish_custom_agent` creates a pending `marketplace_submissions` row, but there is no complete admin approval flow in this reviewed path.

## Current Build Workflow Flow

The Build Workflow button calls `POST /build_workflow` with:

```json
{
  "user_id": "supabase-user-id-or-anonymous",
  "final_agents": ["Digital Spec Agent", "Digital RTL Agent"],
  "preplan": {
    "loop_type": "digital",
    "agents": [],
    "missing_agents": []
  }
}
```

Backend behavior:

- Requires `final_agents`.
- Creates a new preplan internally with `loop_type: "system"`.
- Calls `auto_compose_workflow_graph` with `final_agents`.
- `auto_compose_workflow_graph` builds a simple serial graph and skips re-planning.

Risk:

- The backend currently discards the incoming `preplan.loop_type` and forces `system` in `/build_workflow`.
- The generated workflow can still be saved with the frontend's `preplan.loop_type`, but graph assembly itself does not preserve that loop type.

## Current Risks

1. Generated code writes into production agent directories.

   `generate_missing_agents_batch` writes Python files under `backend/agents/<loop_type>/`. This is not review-only and conflicts with the newer safe Agent Factory policy.

2. User scoping is incomplete and inconsistent.

   Some paths use `owner_id`, some use `user_id`, and `save_custom_agent` does not store an owner id. System Planner lookup does not consistently merge `global agents + current user's private agents` as a first-class planning input.

3. User-created agents can become visible through shared backend files.

   Even if Supabase metadata is owner-scoped, writing generated modules into shared backend directories can make generated code globally available after deployment or reload.

4. Legacy missing-agent generation bypasses Studio Contract metadata.

   It does not produce AgentSpec, SkillSpec, ToolSpec, HookSpec, registry patch plans, or a validation checklist.

5. Missing agents are appended to the end of selected agents.

   The current frontend appends generated agents after `preplan.agents`, which may not preserve intended dependency order.

6. Some frontend state is stored in localStorage.

   `localStorage.custom_agents` can drift from Supabase `agents`.

7. Stale endpoint references exist.

   `/suggest_next_agent` is referenced by frontend canvas interactions, but no backend route was found in the current backend search.

8. Marketplace path is present but not a full governance workflow.

   `publish_custom_agent` inserts a pending marketplace submission, but admin review, approval visibility, rejection notes, and promotion rules are not complete in this flow.

9. Naming and domain support are narrow.

   `MissingAgentNamingDialog` supports a limited domain type and may not represent all backend loop types cleanly.

10. Legacy Planner naming overlaps with newer Studio Agent Planner.

   `frontend/components/AgentPlannerModal.tsx` is actually the System Planner modal, while `frontend/components/studio/AgentPlannerModal.tsx` is the newer Studio Agent Planner.

## Legacy Generate Missing Agents vs New Agent Planner / Factory

Legacy Generate Missing Agents:

- Convenient inside the System Planner flow.
- Generates and saves immediately.
- Writes Python files directly under backend agent directories.
- Saves minimal Supabase metadata.
- Updates capability memory.
- Does not generate Studio Contract metadata.
- Does not require a review step before making artifacts available.

New Studio Agent Planner:

- Uses registry-based deterministic matching.
- Returns exact matches, similar matches, reusable skills/tools/hooks, missing capabilities, recommendation, confidence, and explanation.
- Does not write files or modify registry.
- Better suited for deciding whether to reuse, extend, or create.

New Studio Agent Factory:

- Defaults to dry-run.
- Writes only to safe generated directories when write mode is explicitly enabled.
- Produces proposed AgentSpec, SkillSpec references, ToolSpec references, HookSpec references, generated file plans, registry patch plans, validation checklist, and risks.
- Does not auto-promote to production.
- Better aligned with production review and future marketplace governance.

Recommendation:

- Keep the legacy System Planner UX steps for now.
- Replace the internals of Generate Missing Agents over time with the new Agent Planner and Agent Factory flow.
- Rename the user-facing action later from `Generate Missing Agent` to `Resolve Missing Agents` or `Plan Missing Agents` to emphasize review and user control.
- Treat `generate_missing_agents_batch` as a legacy compatibility path until it can be retired or made review-only.

## Recommended Product Strategy

Global/platform agents:

- Visible to all users.
- Backed by Studio registry metadata and/or platform `agents` rows.
- Maintained by ChipLoop.

User-created agents:

- Private to the creator by default.
- Not visible to other users.
- Not written into global registry YAML automatically.
- Not promoted to marketplace/global automatically.
- Can be used by the creator's System Planner and workflows after save.

System Planner should use:

- Global/platform agents.
- Current user's private agents.
- Never another user's private agents.

Generate Missing Agents should become:

1. Detect missing agent names from Select Agents.
2. For each missing agent, launch the newer Agent Planner with the missing capability context.
3. If recommendation is `reuse_existing`, allow the user to select that existing agent.
4. If recommendation is `extend_existing` or `create_new`, call Agent Factory dry-run.
5. Show generated AgentSpec, skills/tools/hooks, files, registry patch, validation checklist, and risks.
6. Let the user save the reviewed result as a private user agent.
7. Refresh System Planner's available agents.
8. Enable Build Workflow only after all missing agents are resolved.

Build Workflow should use:

- The final selected agent list.
- A lookup context of global agents plus current user's private agents.
- No hidden generation.
- No cross-user private agent access.

## Minimal Data Model

Recommended table: `user_agents`

Fields:

- `id`
- `user_id`
- `name`
- `loop_type`
- `description`
- `agent_spec`
- `skills`
- `tools`
- `hooks`
- `generated_files`
- `registry_patch`
- `status`
- `visibility`
- `source`
- `created_at`
- `updated_at`

Recommended `status` values:

- `draft`
- `private`
- `submitted`
- `approved`
- `rejected`

Recommended `visibility` values:

- `private`
- `global`
- `marketplace`

Optional future marketplace fields:

- `submitted_at`
- `reviewed_at`
- `reviewed_by`
- `review_notes`
- `marketplace_submission_id`
- `pricing_model`
- `revenue_share_basis_points`

Alternative:

- Reuse existing `agents` if it already has `owner_id`, `is_custom`, `is_marketplace`, and enough JSON columns can be added safely.
- If reusing `agents`, standardize on `owner_id` for user scoping and add JSON metadata columns for AgentSpec, skills, tools, hooks, generated files, and review status.

## Minimal Backend Changes Recommended

Add browser-safe, session-authenticated endpoints:

- `GET /studio/user-agents`
  - List only the current user's private agents.

- `POST /studio/user-agents`
  - Save a reviewed Agent Factory dry-run result as a private user agent.
  - Store metadata and generated review artifacts.
  - Do not write into production agent directories.

- `DELETE /studio/user-agents/{id}`
  - Delete or revoke only the current user's private agent.

- `POST /studio/user-agents/{id}/submit`
  - Later phase only.
  - Submit a private agent to marketplace review.

Update System Planner lookup:

- Resolve available agents as:
  - platform registry agents
  - approved/global agents
  - current user's private agents
- Exclude private agents owned by other users.
- Pass the merged catalog into matching/planning deterministically.
- Keep serial execution unchanged.

Normalize existing custom-agent endpoints:

- Use `owner_id` consistently.
- Make `/save_custom_agent` set `owner_id`.
- Fix `/rename_custom_agent` to scope by `owner_id`, not `user_id`.
- Keep `/publish_custom_agent` as a submission-only endpoint until admin approval exists.

Legacy path:

- Keep `/generate_missing_agents_batch` for compatibility initially.
- Mark it as legacy.
- Stop using it from the main System Planner once the Agent Planner/Factory save path exists.
- Avoid direct file writes in future browser-triggered generation flows.

## Minimal Frontend Changes Recommended

Keep the current System Planner flow simple:

1. Analyze Spec.
2. Select Agents.
3. Generate Missing Agents.
4. Build Workflow.

Update Generate Missing Agents behavior:

- If missing agents exist, open a guided resolver.
- Show progress: `Resolving missing agent 1 of N`.
- For each missing agent:
  - Prefill the newer Studio Agent Planner.
  - Run planner.
  - If reusable agent exists, let user select it.
  - If creation is needed, open Agent Factory dry-run.
  - Show review result.
  - Save as private user agent only after user confirmation.
- After all missing agents are resolved, refresh the available agent catalog.
- Re-run or update selected/final agents.
- Enable Build Workflow.

Keep standalone Agent Planner:

- Keep it available for users who want to create or evaluate an agent directly outside the System Planner flow.

Do not expose:

- All 151 platform agents to normal App users.
- Other users' private agents.
- Registry YAML directly.
- Raw production filesystem paths unless intentionally sanitized.
- Write/promote controls without backend governance.

## Marketplace / Global Approval Strategy

Future flow:

1. User creates a private agent.
2. User clicks Submit to Marketplace.
3. Backend creates a `marketplace_submissions` row.
4. Admin reviews generated metadata, implementation notes, tests, risks, and ownership.
5. Admin approves or rejects.
6. Approved agent becomes global and/or marketplace-visible.
7. Rejected agent remains private with review notes.

Do not implement now:

- Stripe.
- Revenue share.
- Auto-approval.
- Auto-merge.
- Auto-registry promotion.

## Exact Files Likely Needing Changes Later

Frontend:

- `frontend/components/AgentPlannerModal.tsx`
- `frontend/components/MissingAgentNamingDialog.tsx`
- `frontend/app/workflow/page.tsx`
- `frontend/components/studio/AgentPlannerModal.tsx`
- `frontend/components/studio/AgentFactoryDryRunModal.tsx`
- `frontend/components/studio/GeneratedAgentReviewModal.tsx`
- `frontend/lib/apiClient.ts`

Backend:

- `backend/main.py`
- `backend/planner/ai_work_planner.py`
- `backend/planner/ai_agent_planner.py`
- `backend/studio_planner/*`
- `backend/studio_factory/*`
- `backend/studio_contract/*`
- `backend/auth_session.py` or equivalent session-auth helper if extended
- New user-agent repository/service module
- `backend/supabase/migrations/*`
- `backend/tests/*`

## Recommended Implementation Order

1. Add or standardize user-agent persistence.
2. Add session-authenticated user-agent list/save/delete endpoints.
3. Make System Planner's available-agent lookup merge global plus current user's private agents.
4. Update Generate Missing Agents to drive the newer Agent Planner and Agent Factory dry-run sequentially.
5. Save reviewed generated agents as private user agents.
6. Enable Build Workflow after all missing agents are resolved.
7. Deprecate direct browser use of `/generate_missing_agents_batch`.
8. Add marketplace submission review as a later phase.

## Summary Recommendation

The current System Planner flow is useful but mixes planning, generation, persistence, and availability in a way that is risky for multi-user production. The clean path is to keep Select Agents as a detector of `selected_agents` and `missing_agents`, then resolve missing agents through the newer Agent Planner and Agent Factory dry-run flow. Generated agents should be saved as private, user-scoped records by default. Global and marketplace visibility should require explicit submission and admin approval.
