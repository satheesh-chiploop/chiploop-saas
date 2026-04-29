# Phase 7H + 7I Frontend Private Agents Flow

## Purpose

Phase 7H + 7I connects Studio missing-agent resolution to the safer Agent Planner and Agent Factory dry-run path. Generated agents are saved as private user agents by default and can be submitted for marketplace review without becoming global automatically.

## Routes And Endpoints

The browser uses session-auth `/api/studio/*` routes only:

- `POST /api/studio/agent-planner/plan`
- `POST /api/studio/agent-factory/dry-run`
- `GET /api/studio/user-agents`
- `POST /api/studio/user-agents`
- `DELETE /api/studio/user-agents/{id}`
- `POST /api/studio/user-agents/{id}/submit`

The UI does not call `/sdk/*`.

## System Planner Flow

The existing System Planner remains modal-based:

1. Analyze Spec
2. Select Agents
3. Resolve Missing Agents
4. Build Workflow

When missing agents exist, the Resolve Missing Agents action opens a guided resolver. The resolver processes missing agents one at a time:

1. Prefills the Agent Planner request from the missing capability, workflow goal, loop type, and spec context.
2. Shows exact and similar reusable agent matches.
3. Lets the user choose an existing agent when reuse is recommended.
4. Runs Agent Factory dry-run when a new or extended agent is needed.
5. Saves reviewed dry-run output as a private user agent.
6. Moves to the next missing agent.

After all missing agents are resolved, the selected agent list is updated, missing agents are cleared, and Build Workflow can continue.

## Private Agents UI

The Studio sidebar now labels user-created agents as `My Agents`. These agents are loaded from the browser-safe user-agents endpoint, so only the signed-in user's private agents are shown.

Supported actions:

- Drag private agents onto the Studio canvas.
- Delete a private agent.
- Submit a private agent for marketplace review.

Submitted agents show a `Submitted` status and the submit action is disabled.

## Generated Agent Review

The Generated Agents review modal remains review-only. It can save the latest Agent Factory dry-run result as a private agent through `POST /api/studio/user-agents`.

The UI still does not auto-promote generated agents, modify registry YAML, merge patches, or write production agent files.

## Validation Steps

1. Open `/workflow`.
2. Run System Planner until missing agents are detected.
3. Click `Resolve Missing Agents`.
4. Confirm planner results appear for each missing capability.
5. Reuse an exact/similar match or run Factory dry-run.
6. Save a generated dry-run as a private agent.
7. Confirm the agent appears under `My Agents`.
8. Submit it for marketplace review and confirm it shows `Submitted`.
9. Delete a private agent and confirm the list refreshes.
10. Build Workflow after missing agents are resolved.

## Known Limitations

- The resolver appends resolved agents after the selected base agents; a later dependency-aware insertion step can preserve exact missing-agent positions.
- Marketplace submission is only a review request. Admin approval and global promotion are intentionally not implemented in the frontend.
- Legacy custom-agent endpoints remain as fallback for older rows that do not have a private agent id.
