# ChipLoop Customer Deployment Runbook

## Deployment Modes

| Mode | Frontend | Backend | Data | Tools | Models |
|---|---|---|---|---|---|
| Hosted SaaS | ChipLoop | ChipLoop | ChipLoop | ChipLoop | ChipLoop |
| Hybrid Private Backend | ChipLoop | Customer | ChipLoop | Customer | Customer |
| Hybrid Private Data | ChipLoop | Customer | Customer | Customer | Customer |
| Private | Customer | Customer | Customer | Customer | Customer |
| Customer Cloud | Customer or ChipLoop | Customer cloud | Customer cloud | Customer | Customer |

Set the active mode with:

```bash
CHIPLOOP_DEPLOYMENT_MODE=hybrid_private_backend
```

## Customer Inputs

Before installation, collect:

- Deployment mode.
- Backend hostname and TLS requirements.
- Database, storage, and authentication endpoints.
- Tool executable paths.
- EDA license environment variables.
- PDK/library mount paths.
- Model provider, model IDs, API keys, or cloud IAM role.
- Artifact policy.
- ChipLoop license mode and license key.
- Network allowlists and proxy requirements.

## Tool Profile

Start from:

```text
backend/config/tool_profiles/hybrid_private_backend_opensource.example.json
```

Production customer profiles should set:

```json
{
  "strict_tool_profile": true
}
```

This prevents agents from silently using tools found on an uncontrolled system PATH.

Common tools:

- Runtime: Python, pip, pytest, cocotb-config.
- Digital: Verilator, Icarus, Yosys, SymbiYosys, Z3, Boolector.
- Embedded/System: make, cargo, rustc, gcc, gem5.
- Commercial: Synopsys Design Compiler, VCS, Cadence Genus, Xcelium.

## Model Profile

Model profiles are mounted with:

```bash
CHIPLOOP_MODEL_PROFILE_PATH=/etc/chiploop/model_profile.json
```

Examples:

- `customer_byok_openai.example.json`
- `customer_azure_openai.example.json`
- `customer_aws_bedrock.example.json`
- `customer_openai_compatible.example.json`
- `customer_mixed_models.example.json`

Customers own API keys, cloud IAM roles, model access, quotas, and licenses for customer-managed deployments.

## Platform Data Services

Supabase remains the default provider and is the lowest-risk private deployment option. ChipLoop now also supports independent provider selection for:

- Database: Supabase/PostgREST or PostgreSQL.
- Storage: Supabase Storage, local filesystem, S3, MinIO, or Azure Blob.
- Authentication: Supabase Auth or OIDC-compatible providers such as Okta, Auth0, Azure AD, or Entra ID.

Set:

```bash
SUPABASE_URL=
SUPABASE_SERVICE_ROLE_KEY=
NEXT_PUBLIC_SUPABASE_URL=
NEXT_PUBLIC_SUPABASE_ANON_KEY=
```

Alternative example profiles are available under `backend/config/platform_profiles`.

For PostgreSQL deployments, apply the same ChipLoop schema used by Supabase before starting the backend. PostgreSQL support preserves the common table query contract; Supabase-specific RPC calls require Supabase/PostgREST unless separately migrated.

The frontend supports two platform modes:

- `supabase` keeps the hosted SaaS behavior and uses Supabase sessions and realtime directly.
- `backend` uses the authenticated backend platform API for sessions, workflow queries, storage downloads, and polling-based live updates.

For a PostgreSQL/OIDC deployment, set `CHIPLOOP_FRONTEND_PLATFORM_PROVIDER=backend_platform_api` and build the frontend with `NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER=backend`. Route browser `/api/*` traffic to the backend so secure OIDC cookies remain same-origin.

## Artifact Policy

Set:

```bash
CHIPLOOP_ARTIFACT_POLICY=private_storage
CHIPLOOP_PRIVATE_ARTIFACT_ROOT=/var/lib/chiploop/artifacts
```

Supported policies:

- `full_sync`: upload all artifacts to configured shared storage.
- `summary_only`: sync text reports and summaries; keep other artifacts private.
- `manifest_only`: sync only manifest/summary/report-style text artifacts.
- `private_storage`: keep artifacts on the private backend.
- `full_private`: keep artifacts private.
- `customer_cloud_storage`: keep artifacts in customer cloud storage.

## Licensing

ChipLoop application licensing and EDA tool licensing are separate:

- Hosted SaaS uses the existing ChipLoop subscription and billing system.
- Hybrid Private Backend deployments use a ChipLoop hybrid-private-backend license.
- Private and customer-cloud deployments use a ChipLoop enterprise license key supplied to the customer.
- Synopsys, Cadence, Siemens, PDK, and other third-party licenses remain customer-managed and are passed through environment variables or the customer secret manager.

Set:

```bash
CHIPLOOP_LICENSE_MODE=private_enterprise
CHIPLOOP_LICENSE_KEY=
```

## Installation

Use one package:

- `deploy/hybrid-private-backend`
- `deploy/private`
- `deploy/customer-cloud`

Mount tools, PDKs, repositories, and profile files read-only where possible.

For a ChipLoop-hosted frontend and Supabase customer, follow the detailed release and onboarding procedure in:

```text
docs/HYBRID_PRIVATE_BACKEND_CUSTOMER_RELEASE_GUIDE.md
```

## Diagnostics

From the backend container:

```bash
curl http://127.0.0.1:8000/ready
python -m chiploop_sdk.support_bundle
```

In the UI, open:

```text
Settings > Deployment
```

Review:

- Active deployment mode.
- Model profile/provider.
- Tool profile, backend execution environment, and artifact policy.
- Tool paths and availability.
- Tool adapter registry.
- Tool diagnostics output.

## Acceptance Tests

Run these in order:

1. PWM Arch2RTL.
2. PWM Verify with Verilator coverage and optional SymbiYosys.
3. PWM Embedded Firmware and co-simulation.
4. System Architecture gem5 X86.
5. System Architecture gem5 RISC-V.
6. Smart Sensor Hub Arch2RTL.
7. Download or inspect artifacts according to the selected artifact policy.

## Support Bundle

The support bundle contains deployment metadata, model profile summary, artifact policy, and tool diagnostics. It does not include RTL/spec artifacts or API keys.
