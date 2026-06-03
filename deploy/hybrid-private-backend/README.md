# ChipLoop Hybrid Private Backend

This package runs the complete ChipLoop backend inside the customer network while
ChipLoop hosts the customer-specific frontend and Supabase control plane.

It supports full reference journeys because workflow agents, model calls, and
customer tools execute in one private backend process.

## Data Boundary

- Customer tools, licenses, mounted repositories, and backend execution stay in the customer network.
- Workflow records and artifacts are synchronized to ChipLoop-hosted Supabase according to `CHIPLOOP_ARTIFACT_POLICY`.
- This mode is not appropriate for customers that prohibit specs or artifacts from reaching ChipLoop-hosted Supabase. Use Hybrid Private Data or ChipLoop Private for that requirement.

## Customer Prerequisites

- Linux x86-64 server with Docker Engine and Docker Compose v2
- Outbound HTTPS access to the ChipLoop Supabase project and selected model provider
- Inbound HTTPS access from the assigned ChipLoop frontend origin
- Customer tool installations, license servers, and model API credentials
- At least 8 vCPU, 32 GB RAM, and 200 GB persistent disk for reference journeys

## Install

1. Copy this directory to the customer server.
2. Create `.env.backend` from `.env.backend.example`.
3. Set the release image tag, ChipLoop-issued license key, Supabase credentials, allowed frontend origin, and model credentials.
4. Edit `tool_profile.json` so every executable points to the customer-mounted tool path.
5. Edit `model_profile.json` for the customer model provider and per-agent routing policy.
6. Add read-only tool, PDK, and repository mounts to `docker-compose.backend.yml`.
7. Start the backend:

   ```bash
   docker compose -f docker-compose.backend.yml --env-file .env.backend up -d
   ```

8. Verify:

   ```bash
   curl http://127.0.0.1:8000/health
   curl http://127.0.0.1:8000/ready
   ```

`/ready` must report healthy data store, tool profile, model profile, and license checks.

## ChipLoop Onboarding Actions

ChipLoop provisions a customer-scoped Supabase tenant/identity boundary, issues the
hybrid license, creates a customer-specific Vercel frontend deployment, and sets:

```text
CHIPLOOP_API_BASE_URL=https://chiploop-backend.customer.example
```

The backend must set:

```text
CHIPLOOP_ALLOWED_ORIGINS=https://customer-name.getchiploop.com
```

The UI remains the same because the customer frontend deployment uses the same
ChipLoop frontend source and only changes the `/api` destination.

## Acceptance Test

Run these from the hosted customer frontend:

1. PWM Controller reference journey through Arch2RTL, Verify, Firmware, Software, Validation, and Product App.
2. System Architecture Explorer with a gem5 X86 or RISC-V sweep.
3. Download ZIP and Ask This Run.
4. Settings > Deployment tool and model diagnostics.

Commercial EDA adapters require customer-specific acceptance tests before they are
declared supported for production.
