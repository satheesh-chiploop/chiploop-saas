# Phase 7B Settings UI

## Routes Added

- `/settings`
- `/settings/api-keys`
- `/settings/usage`

The `/settings` route redirects to `/settings/api-keys`.

## Backend Endpoints Used

Frontend calls use relative `/api` routes so Vercel rewrites can forward requests to the backend:

- `GET /api/settings/api-keys`
- `POST /api/settings/api-keys`
- `POST /api/settings/api-keys/{id}/revoke`
- `GET /api/settings/usage`

The browser does not call `/sdk/*`.

## Auth Behavior

- `middleware.ts` now protects `/settings/:path*` in addition to `/apps/:path*` and `/workflow/:path*`.
- `lib/apiClient.ts` gets the current Supabase session and sends `Authorization: Bearer <access_token>`.
- If the backend returns `401`, Settings pages show a session-expired error state.

## Raw API Key Handling

- Raw API keys are displayed only immediately after creation.
- Raw keys are not written to localStorage or persisted in frontend state beyond the visible page session.
- API key list responses display metadata only: name, prefix, created time, last-used time, and revoked status.

## UI Behavior

API Keys:

- Shows loading, empty, error, active, and revoked states.
- Allows users to create a named test API key.
- Shows the raw key in a copyable box once.
- Requires confirmation before revoking a key.
- Refreshes the metadata table after create/revoke.

Usage:

- Shows recent event count.
- Shows event type breakdown.
- Shows recent usage events with endpoint, event type, timestamp, and workflow id.
- Does not include billing, Stripe, credit ledger, or plan controls.

## Navigation

Settings is linked from:

- `/apps`
- `/workflow`

Existing navigation entries were preserved.

## Test Steps

Run:

```bash
npm run lint
npm run build
```

Manual checks:

- `/apps` still loads.
- `/workflow` still loads.
- `/settings/api-keys` redirects unauthenticated users to `/login`.
- `/settings/api-keys` loads for an authenticated user.
- Creating a key shows the raw key once.
- Refreshing the page removes the raw key display.
- Revoking a key updates its status.
- `/settings/usage` loads usage summary and recent events.

## Known Limitations

- API key creation currently sends `environment: "test"`.
- No billing or Stripe UI is included.
- Usage display is limited to the fields returned by the Phase 7A backend.
- Settings pages rely on Supabase browser session availability.

## Next Steps

- Add Studio Agent Planner UI.
- Add Agent Factory dry-run review UI.
- Add DAG preview UI.
- Keep normal Apps curated and separate from raw agent registry details.
