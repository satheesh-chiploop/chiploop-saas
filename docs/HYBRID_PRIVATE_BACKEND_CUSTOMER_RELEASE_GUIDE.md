# Hybrid Private Backend Customer Release Guide

## Purpose

Hybrid Private Backend is the production deployment for customers who want the
normal ChipLoop hosted user experience but require workflow execution, tools,
commercial EDA licenses, and model API keys to run inside their network.

The deployment boundary is:

| Component | Owner |
|---|---|
| Customer-specific ChipLoop frontend | ChipLoop |
| ChipLoop Supabase database/auth/storage | ChipLoop |
| ChipLoop backend and agents | Customer |
| Open-source and commercial tools | Customer |
| Tool and PDK licenses | Customer |
| Model provider account and API keys | Customer |

The frontend look and feel is the same as hosted SaaS because it uses the same
frontend source. The only frontend change is that `/api` routes to the customer's
private backend instead of `api.getchiploop.com`.

## Important Data Boundary

This mode still uses ChipLoop-hosted Supabase. Workflow metadata, user identity,
and artifacts allowed by the selected artifact policy can reach ChipLoop-hosted
services.

Do not sell this mode as zero-data-egress. Customers that require database,
storage, and authentication to remain private need Hybrid Private Data or the
fully self-hosted ChipLoop Private package.

## What ChipLoop Must Prepare

1. Create a customer deployment record and commercial entitlement.
2. Issue a Hybrid Private Backend license key.
3. Provision a dedicated or contractually isolated Supabase tenant boundary.
4. Create the customer frontend Vercel project from the standard ChipLoop frontend.
5. Set the Vercel build environment:

   ```text
   CHIPLOOP_API_BASE_URL=https://chiploop-backend.customer.example
   ```

6. Assign the customer frontend hostname:

   ```text
   https://customer-name.getchiploop.com
   ```

7. Provide the customer:

   - Signed backend image tag and digest
   - `deploy/hybrid-private-backend` package
   - Supabase URL, service credential, and JWT secret using the agreed tenant boundary
   - License key
   - Supported tool/profile matrix
   - Support and upgrade contacts

8. Add the customer's backend hostname to any required network allowlists.

## What the Customer Must Prepare

1. Linux x86-64 server or VM with Docker Engine and Docker Compose v2.
2. DNS and TLS for:

   ```text
   https://chiploop-backend.customer.example
   ```

3. Inbound HTTPS access from the ChipLoop-hosted frontend.
4. Outbound HTTPS access to:

   - ChipLoop Supabase endpoint
   - Customer-selected model provider
   - Optional package registries required by their workflows

5. Tool installations and executable paths.
6. Commercial EDA, PDK, and license server access where applicable.
7. Customer-owned model account, API keys, quotas, and billing.
8. Backup and monitoring for the backend host and any customer-local artifacts.

## Recommended Host Size

For reference journeys:

```text
8 vCPU
32 GB RAM
200 GB persistent disk
Ubuntu 24.04 LTS or equivalent
```

Increase resources for large gem5 sweeps, commercial synthesis, or concurrent users.

## Customer Installation

1. Copy the release package to the customer server.

2. Create the runtime environment file:

   ```bash
   cd deploy/hybrid-private-backend
   cp .env.backend.example .env.backend
   ```

3. Set these required values:

   ```text
   CHIPLOOP_IMAGE_TAG=<release-tag-from-chiploop>
   CHIPLOOP_LICENSE_KEY=<license-key-from-chiploop>
   SUPABASE_URL=<provided-by-chiploop>
   SUPABASE_SERVICE_ROLE_KEY=<provided-by-chiploop>
   SUPABASE_JWT_SECRET=<provided-by-chiploop>
   CHIPLOOP_ALLOWED_ORIGINS=https://customer-name.getchiploop.com
   OPENAI_API_KEY=<customer-key>
   ```

4. Edit `tool_profile.json`. Keep `strict_tool_profile` enabled and point each
   executable to a mounted customer path.

5. Edit `model_profile.json` for the customer provider and model routing policy.
   Per-agent model overrides are supported under the `agents` object.

   For customer-paid model accounts:

   ```json
   {
     "ai_billing_mode": "byok",
     "model_key_owner": "customer"
   }
   ```

   For ChipLoop-managed model credits:

   ```json
   {
     "ai_billing_mode": "chiploop_managed",
     "model_key_owner": "chiploop"
   }
   ```

   ChipLoop-managed mode records model usage events and pooled AI-credit ledger
   debits in Supabase. BYOK records usage for audit/reporting but does not debit
   ChipLoop AI credits.

6. Add read-only mounts for tools, PDKs, and repositories to
   `docker-compose.backend.yml`.

7. Authenticate to the ChipLoop container registry using the credential supplied
   under the commercial agreement.

8. Start the backend:

   ```bash
   docker compose -f docker-compose.backend.yml --env-file .env.backend pull
   docker compose -f docker-compose.backend.yml --env-file .env.backend up -d
   ```

9. Verify health:

   ```bash
   curl https://chiploop-backend.customer.example/health
   curl https://chiploop-backend.customer.example/ready
   ```

10. Send the `/ready` output to ChipLoop before frontend activation. Do not send
    API keys, license keys, RTL, specs, or customer artifacts.

## License Model

ChipLoop application licensing and third-party tool licensing are separate.

- ChipLoop issues a Hybrid Private Backend entitlement for the customer backend.
- The customer places the key in `CHIPLOOP_LICENSE_KEY`.
- Synopsys, Cadence, Siemens, PDK, model provider, and other third-party licenses
  remain customer-managed.
- Image registry access, support term, user limits, and permitted deployment count
  should be defined in the commercial agreement.

For the first production release, treat license enforcement as an entitlement and
support control in addition to the configured key. Do not depend on the key alone
as a security boundary.

## Frontend Activation

After the customer backend is healthy:

1. ChipLoop sets `CHIPLOOP_API_BASE_URL` in the customer Vercel project.
2. ChipLoop redeploys the frontend.
3. The customer backend sets:

   ```text
   CHIPLOOP_ALLOWED_ORIGINS=https://customer-name.getchiploop.com
   ```

4. ChipLoop and the customer confirm browser login, workflow creation, run status,
   artifact download, and Ask This Run.

One global ChipLoop frontend deployment cannot route different customers to
different private backend URLs. Each Hybrid Private Backend customer needs a
customer-specific frontend deployment or an equivalent tenant-aware API gateway.

## Reference Journey Acceptance Test

Run the following in the customer frontend:

1. PWM Controller Arch2RTL.
2. Verify with Verilator coverage and optional SymbiYosys.
3. Embedded Firmware co-simulation.
4. System Software.
5. Software Validation.
6. Product App Builder.
7. System Architecture Explorer using gem5 X86.
8. System Architecture Explorer using gem5 RISC-V.
9. Download ZIP.
10. Ask This Run.
11. Settings > Deployment tool diagnostics.
12. Settings > Deployment model diagnostics.

The same agents and generated dashboards are used as hosted SaaS. Results can
differ when the customer selects different tools, tool versions, PDKs, or models.

## Commercial Tool Acceptance

Do not claim a Synopsys or Cadence flow is supported only because the executable is
visible. A customer-specific acceptance test must confirm:

- Adapter command template
- Required environment variables
- Library and PDK mounts
- License checkout
- Script generation
- Log parsing
- Artifact extraction
- Dashboard mapping
- Failure handling

## Operations

Customer responsibilities:

- Backend host uptime, TLS, firewall, secrets, tools, licenses, and model quotas
- Monitoring container health and disk usage
- Backing up customer-local artifacts
- Applying approved backend image updates

ChipLoop responsibilities:

- Hosted frontend, hosted Supabase, application support, signed backend images,
  release notes, and entitlement management

## Upgrade and Rollback

1. ChipLoop supplies a new signed image tag and digest.
2. Customer validates it in a staging backend.
3. Customer updates `CHIPLOOP_IMAGE_TAG`.
4. Customer pulls and restarts the service.
5. Customer reruns the PWM reference acceptance test.
6. To roll back, restore the previous image tag and restart.

Never deploy `latest` in a customer environment.
