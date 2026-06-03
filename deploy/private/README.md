# Full Private Deployment

This package is for customers who host ChipLoop entirely inside their environment.

## Customer Owns

- Frontend hosting.
- Backend/runtime.
- Customer-managed platform services: Supabase by default, or PostgreSQL plus local/S3 storage and OIDC.
- Model provider keys.
- EDA tools, PDKs, licenses, and internal repositories.

## Install

```bash
cp .env.private.example .env.private
cp ../../backend/config/tool_profiles/customer_private_runner.example.json tool_profile.json
cp ../../backend/config/model_profiles/customer_azure_openai.example.json model_profile.json
docker compose -f docker-compose.private.yml up -d
```

## Platform Requirements

The recommended first deployment uses customer-managed or self-hosted Supabase:

- `SUPABASE_URL`
- `SUPABASE_SERVICE_ROLE_KEY`
- `NEXT_PUBLIC_SUPABASE_URL`
- `NEXT_PUBLIC_SUPABASE_ANON_KEY`
- `CHIPLOOP_MODEL_PROFILE_PATH`
- `CHIPLOOP_TOOL_PROFILE_PATH`

Alternative providers are supported through:

- `CHIPLOOP_DATABASE_PROVIDER=postgresql`
- `CHIPLOOP_STORAGE_PROVIDER=local_fs`, `s3`, or `minio`
- `CHIPLOOP_AUTH_PROVIDER=oidc`
- `CHIPLOOP_FRONTEND_PLATFORM_PROVIDER=backend_platform_api`
- `NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER=backend`

PostgreSQL must be initialized with the ChipLoop schema before backend startup. Supabase-specific RPC features still require Supabase/PostgREST unless separately migrated.

For a non-Supabase UI deployment, configure the OIDC issuer, client ID, authorization endpoint, and token endpoint. The frontend uses the authenticated backend platform API for workflow data and polls it for live updates. Route browser `/api/*` traffic to the backend so secure OIDC cookies remain same-origin.

`NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER` is a frontend build-time variable. Build or select the backend-platform frontend image for PostgreSQL/OIDC deployments.

## Validation

```bash
docker compose -f docker-compose.private.yml exec backend python -m chiploop_sdk.runner_healthcheck
docker compose -f docker-compose.private.yml exec backend python -m chiploop_sdk.support_bundle
```

Set `"strict_tool_profile": true` in the mounted tool profile before production use.
