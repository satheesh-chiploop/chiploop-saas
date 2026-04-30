# Phase 8B Pricing and Plan UI

Phase 8B updates the frontend to match the backend Phase 8A plan and entitlement foundation. It does not add Stripe checkout or change App/Studio workflow execution.

## Routes Updated

- `/pricing`
  - Replaces legacy Freemium / Single Loop / Double Loop / All Loops cards.
  - Shows Free, Starter, Pro, Pro Max, and Enterprise.
  - Shows monthly credits and a feature comparison table.
  - Upgrade buttons are placeholders. Enterprise uses contact-sales.

- `/settings/plan`
  - Calls `GET /api/settings/plan`.
  - Shows current plan, monthly credits, used credits, remaining credits, enabled features, and billing status placeholder.

- `/settings`
  - Redirects to `/settings/plan`.

- Settings navigation
  - Adds Plan alongside API Keys and Usage.

## Backend Endpoint Used

Browser calls use the existing rewrite path:

```text
GET /api/settings/plan
```

The browser does not call `/sdk/*` and does not require users to paste SDK API keys.

## Plan List

- Free: `$0`, 100 credits/month
- Starter: `$29/month`, 1,000 credits/month
- Pro: `$99/month`, 5,000 credits/month
- Pro Max: `$249/month`, 12,000 credits/month
- Enterprise: Custom, custom credits

There is no Team plan.

## Safety Rules

- No Stripe integration in this phase.
- No real checkout or portal flow.
- No secrets exposed.
- Existing Apps and Studio routes are unchanged.
- Pricing is informational until billing checkout is implemented.

## Validation

Manual checks:

1. `/pricing` loads and shows the five Phase 8 plans.
2. `/settings/plan` loads when authenticated.
3. `/settings` redirects to `/settings/plan`.
4. Settings tabs show Plan, API Keys, and Usage.
5. `/apps` still loads.
6. `/workflow` still loads.

Known risk: `/settings/plan` requires the backend Phase 8A endpoint and an authenticated Supabase session.
