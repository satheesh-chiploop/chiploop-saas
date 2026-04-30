# Agent Planner Simplification

## Goal

Keep Studio simple by removing Generated Agents as a separate top-level panel. Generated agent review now belongs inside the Agent Planner flow.

## Current Flow

1. User opens Studio.
2. User clicks Agent Planner.
3. Planner checks for reusable agents first.
4. If a new or extended agent is needed, user clicks Generate Draft Agent.
5. The draft is reviewed in the same flow.
6. User can save it as a private agent.

## UX Rules

- No Generated Agents sidebar entry.
- No standalone generated-agent panel for normal users.
- Raw AgentSpec and registry details stay under Advanced Details.
- Save creates a private user agent only.
- No global promotion, registry write, or marketplace approval happens from this flow.

## Why

A separate Generated Agents panel makes users think generated code is a primary workspace. The product model should be task-based: plan, draft, review, save privately. Marketplace and admin approval remain later flows.

## Validation

- `/workflow` loads with the left sidebar kept tidy.
- Buttons remain focused on Design Intent Planner, System Planner, Agent Planner, and Optimize Workflow.
- Agent Planner can open the draft flow.
- Draft review can save a private agent.
- Existing workflow execution is unchanged.
