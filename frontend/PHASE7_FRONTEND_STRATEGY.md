# Phase 7 Frontend Integration Strategy

## Scope

Phase 7 should integrate the backend platform work without changing the current App execution experience. The frontend already has a useful separation:

- Apps are curated, simple workflow runners for normal users.
- Studio is the power-user workspace at `/workflow`.
- Authentication is Supabase-based.
- Backend workflow execution remains the source of truth.

This document is a strategy only. It does not require production UI changes yet.

## Current Frontend Architecture

### Framework and Structure

- Framework: Next.js App Router with React client components.
- Main directories:
  - `app/` for routes and pages.
  - `components/` for Studio planner modals.
  - `app/workflow/` for Studio canvas, node UI, console, and results.
  - `app/apps/` for curated app runners.
  - `hooks/` for voice/spec helper integrations.
  - `lib/` for Supabase client setup.
  - `utils/` for user identity helpers.

### Existing Routes

Apps:

- `/apps`
- `/apps/[app_slug]`
- Dedicated app pages under `/apps/*`, including digital, analog, embedded, validation, and system flows.
- The Apps home is curated and does not expose all registered agents.

Studio:

- `/workflow`
- Current Studio contains a ReactFlow-based workflow canvas, custom agent/workflow management, validation utilities, workflow execution, and planner modals.

System Planner:

- `components/PlannerModal.tsx`
- `components/AgentPlannerModal.tsx`
- `components/MissingAgentNamingDialog.tsx`
- The modal flow calls planning, spec analysis, workflow build, save workflow, and missing-agent generation endpoints.

Pricing:

- `/pricing`
- Current pricing page contains plan cards and placeholder/legacy checkout portal calls. Phase 7 should leave this page unchanged until billing is intentionally implemented.

Login/auth:

- `/login`
- `/auth/callback`
- `middleware.ts` protects only `/apps/:path*` and `/workflow/:path*`.

### Current API and Data Access

Environment variables referenced by source:

- `NEXT_PUBLIC_SUPABASE_URL`
- `NEXT_PUBLIC_SUPABASE_ANON_KEY`
- `NEXT_PUBLIC_API_URL`
- `NEXT_PUBLIC_BACKEND_URL`
- `NEXT_PUBLIC_BACKEND_WS_URL`

Direct Supabase usage:

- Auth session/user checks.
- Realtime subscriptions against `workflows` and `runs`.
- Reads from `agents`, `workflows`, `design_intent_drafts`, and validation tables.
- Supabase Storage signed URLs from `artifacts`.

Backend calls observed:

- App run endpoints such as `/apps/arch2rtl/run`, `/apps/validation/run`, `/apps/analog/run`, `/apps/embedded/run`, and `/apps/system/*/run`.
- Studio execution endpoint `/run_workflow`.
- Artifact endpoint `/workflow/{workflow_id}/download_zip`.
- Planner/spec endpoints: `/plan_workflow`, `/analyze_spec`, `/auto_compose_workflow`, `/build_workflow`, `/save_custom_workflow`, `/generate_missing_agents_batch`.
- Custom agent/workflow endpoints: save, rename, delete, publish, get code, save code.
- Validation endpoints for instruments, benches, test plans, previews, and probes.

Important integration note:

- Several components call relative `/api/...` endpoints, but no visible frontend `app/api` route handlers were found during inspection.
- Many app pages call `NEXT_PUBLIC_API_URL` directly.
- Phase 7 should standardize this boundary with a small frontend API client and/or Next route handlers, without changing current endpoint behavior.

## Backend Capability Compared To Frontend

Backend capabilities now available:

- Agent Runtime Contract v1 routes all agents through common execution.
- Studio Contract v1 has registry metadata for 151 agents, 12 skills, 11 tools/plugins, 6 hooks, 6 workflows, and 2 commands.
- Agent Planner can recommend reuse, extension, composition, or creation.
- Agent Factory can safely generate dry-run plans and write only to safe generated directories.
- SDK/CLI endpoints exist under `/sdk/*` and are API-key protected.
- API key and usage tracking exists for SDK/CLI endpoints.
- Workflow DAG exists as opt-in planning/execution infrastructure; serial behavior remains default.
- Phase 6 persistence migrations/repositories exist for production persistence.

Frontend gaps:

- No API key management UI.
- No usage dashboard.
- No Studio UI for the new deterministic Agent Planner result shape.
- No safe Agent Factory dry-run review UI.
- No DAG preview UI.
- No generated agent review/promote workflow.
- No clear browser-safe endpoint family for Studio registry/planner/factory calls separate from API-key SDK endpoints.

## Product Separation

### App Section

Keep Apps simple and curated.

Recommended behavior:

- Keep `/apps` as the main normal-user launch surface.
- Keep dedicated app runners unchanged initially.
- Continue showing curated workflow products, not registry internals.
- Do not expose all 151 registered agents in Apps.
- Continue using existing workflow endpoints and Supabase realtime progress.

### Studio Section

Studio should be the power-user surface.

Recommended behavior:

- Keep `/workflow` as the current Studio canvas.
- Add Studio subviews incrementally instead of replacing the canvas.
- Treat planner, factory, DAG preview, and generated-agent review as Studio tools.
- Hide write-mode factory actions until backend entitlement and review flows are complete.

### Settings/API Key Section

API keys are developer/automation settings, not normal App workflow controls.

Recommended behavior:

- Add a protected settings page for API keys.
- Use Supabase session auth in the browser, not SDK API-key auth.
- API keys should be displayed once at creation and never stored raw in the frontend.
- Revoke should be available before create/delete key flows are promoted.

### Usage Section

Usage should be informational first.

Recommended behavior:

- Show SDK/CLI usage events and workflow run summaries.
- Keep pricing and billing out of Phase 7.
- Do not expose internal credit-ledger details until the product model is finalized.

### DAG Preview Section

DAG belongs in Studio as an optional planning preview.

Recommended behavior:

- Add a dry-run DAG preview that shows nodes, edges, parallel groups, and dependency warnings.
- Do not make DAG execution the default.
- Do not expose DAG executor controls to normal App users.

### Generated Agent Review Section

Generated agents should remain reviewable, not automatically promoted.

Recommended behavior:

- Show generated file plans, registry patch YAML, tests, and migration notes.
- Provide copy/download/review actions.
- Do not auto-write into production agent directories.
- Do not auto-merge registry patches.

## Minimal Route Additions

Prefer adding a small number of protected routes or Studio tabs:

- `/settings/api-keys`
- `/settings/usage`
- `/workflow/planner`
- `/workflow/factory`
- `/workflow/dag-preview`
- `/workflow/generated-agents`

Alternative lower-risk first step:

- Keep all Studio features under `/workflow` as tabs or panels.
- Add only `/settings/api-keys` and `/settings/usage` as new top-level routes.

If `/settings/*` routes are added, update middleware protection to include `/settings/:path*`.

## Existing Pages To Keep Unchanged Initially

- `/apps`
- All existing `/apps/*` dedicated app pages.
- `/workflow` canvas and existing custom workflow behavior.
- `/login`
- `/auth/callback`
- `/pricing`
- Existing Supabase realtime workflow progress UI.
- Existing artifact download behavior.

## What To Hide From Normal Users

- Full registry of 151 agents.
- Raw registry YAML.
- Agent Factory write mode.
- Generated patches and generated source files unless inside Studio.
- DAG executor controls.
- Internal hook/tool/skill metadata.
- API usage event internals beyond a user-readable usage summary.
- Billing, Stripe, credit ledger, and plan enforcement internals.

## Required Backend Endpoints

### Existing Endpoints Frontend Can Continue Using

Apps:

- `POST /apps/*/run`
- `POST /run_workflow`
- `GET /workflow/{workflow_id}/download_zip`

Studio planner/current workflow:

- `POST /plan_workflow`
- `POST /analyze_spec`
- `POST /auto_compose_workflow`
- `POST /build_workflow`
- `POST /save_custom_workflow`
- Existing custom agent/workflow save, rename, delete, publish endpoints.

SDK/CLI:

- `GET /sdk/agents`
- `GET /sdk/workflows`
- `GET /sdk/workflows/{workflow_id}/status`
- `POST /sdk/studio/plan-agent`
- `POST /sdk/studio/generate-agent`

### Missing Or Needed For Browser Studio

The `/sdk/*` endpoints are API-key protected and are appropriate for SDK/CLI. Browser Studio should not require users to paste SDK keys into the frontend. Add session-authenticated backend endpoints or Next route handlers for:

- `GET /studio/registry/summary`
- `GET /studio/registry/agents?scope=studio`
- `POST /studio/agent-planner/plan`
- `POST /studio/agent-factory/dry-run`
- `GET /studio/generated-agents`
- `GET /studio/generated-agents/{id}`
- `POST /studio/dag/preview`
- `POST /studio/dag/validate`
- `GET /settings/api-keys`
- `POST /settings/api-keys`
- `POST /settings/api-keys/{id}/revoke`
- `GET /settings/usage`

Possible legacy endpoint risk:

- `/suggest_next_agent` is referenced in Studio UI. Confirm whether it is still implemented before building new Studio panels around it.

## Phase 7 Plan

### Phase 7A: Navigation And Information Architecture

Goals:

- Keep App and Studio visibly separate.
- Add protected Settings entry for developer controls.
- Avoid exposing backend registry complexity to normal App users.

Implementation order:

1. Add a lightweight navigation model: Apps, Studio, Settings.
2. Add protected route shells for Settings and optional Studio subroutes.
3. Add a shared frontend API helper that centralizes `NEXT_PUBLIC_API_URL` behavior.
4. Preserve existing page behavior while new panels are inactive.

### Phase 7B: API Keys And Usage UI

Goals:

- Let developers create, view metadata for, and revoke SDK/CLI API keys.
- Show basic usage events and workflow status history.

Backend needed:

- Session-auth API-key CRUD endpoints.
- Session-auth usage summary/list endpoint.

Frontend behavior:

- Show key prefix, name, created time, last used time, revoked state.
- Show raw key only once after creation.
- Never store raw key in local storage.

### Phase 7C: Studio Planner UI

Goals:

- Expose the new Agent Planner result in Studio.
- Show exact matches, similar matches, reusable skills/tools/hooks, missing capabilities, recommendation, confidence, and explanation.

Backend needed:

- Browser-safe session-auth planner endpoint or Next route proxy.

Frontend behavior:

- Start as a panel in Studio.
- Do not mutate registry.
- Do not generate files.
- Offer next action only as a dry-run Agent Factory request.

### Phase 7D: Agent Factory Dry-Run UI

Goals:

- Let Studio users review safe generated plans before any write action.

Backend needed:

- Browser-safe dry-run endpoint for Agent Factory.

Frontend behavior:

- Show proposed `AgentSpec`, skills, tools, hooks, generated files, registry patch, checklist, and risks.
- Default to dry-run.
- Hide write mode unless entitlement explicitly allows it.
- Do not auto-promote generated files.

### Phase 7E: DAG Preview UI

Goals:

- Show optional DAG structure for planned workflows.

Backend needed:

- DAG preview/dry-run endpoint.
- DAG validation endpoint.

Frontend behavior:

- Show serial order and DAG parallel groups side-by-side.
- Show dependency errors before execution.
- Make DAG opt-in and preview-only at first.
- Keep current serial App workflows unchanged.

### Phase 7F: Generated Agent Review UI

Goals:

- Provide a review surface for generated stubs and registry patches.

Backend needed:

- List/read generated agent output directories or persisted generated-agent records.
- Optional manual promotion endpoint should be deferred until review governance is clear.

Frontend behavior:

- Show files, diffs/patches, tests, README/migration notes.
- Do not write into `agents/` or `registry/` from the browser.
- Treat promotion as a manual developer operation initially.

## Risks

- Mixed API boundary: direct backend URL calls and relative `/api/...` calls are both used today.
- Browser Studio cannot safely call `/sdk/*` directly unless the user provides an SDK key, which is not the right product model.
- Existing Studio page is large and stateful; replacing it would be high risk.
- Pricing page has checkout/portal hooks but billing is intentionally out of scope.
- Some routes referenced in navigation, such as marketplace or legal pages, may not exist yet.
- Direct Supabase table access in the frontend may limit future authorization changes.
- DAG execution must remain opt-in; surfacing it too early could imply behavior guarantees that are not product-ready.

## Recommended Implementation Order

1. Add protected Settings shells and middleware coverage.
2. Add a shared frontend API client without changing existing behavior.
3. Add backend browser-safe Studio/settings endpoints.
4. Build API Keys UI.
5. Build Usage UI.
6. Add Studio Planner panel.
7. Add Agent Factory dry-run review panel.
8. Add DAG preview panel.
9. Add generated agent review panel.
10. Only after review workflows mature, consider controlled promotion flows.

## Non-Goals For Phase 7

- No billing or Stripe implementation.
- No full marketplace launch.
- No exposure of all registered agents to normal App users.
- No default DAG execution.
- No production agent auto-generation.
- No frontend rewrite.
- No changes to existing App workflow behavior.
