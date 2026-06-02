# ChipLoop Deployment Modes

ChipLoop supports three deployment modes. The hosted SaaS mode remains the default; hybrid and full-private modes are packaging/configuration extensions around the same workflow and agent contracts.

## 1. Hosted SaaS

- Frontend: ChipLoop Vercel deployment.
- Backend/runtime: ChipLoop-managed backend on DigitalOcean.
- Database/storage/auth: ChipLoop Supabase.
- Tools: ChipLoop-managed open-source/default tools through `chiploop_saas_default` tool profile.
- Model keys: ChipLoop-managed provider keys unless user-level API keys are enabled.

Use this for public SaaS users and demos.

## 2. Hybrid Private Runner

- Frontend/backend control plane can remain ChipLoop-hosted.
- Customer runs a private runner container inside their network.
- Customer tools, PDKs, RTL repos, license servers, and private artifacts remain local.
- Runner uses a customer tool profile, for example `/etc/chiploop/tool_profile.json`.
- Artifact policy can be `full_sync`, `summary_only`, or `metadata_only`.

Use this when a customer wants ChipLoop SaaS UX but cannot expose EDA tools, licenses, repos, or full artifacts.

## 3. Full Private Deployment

- Customer hosts frontend, backend, database, storage, auth, runner, and tools.
- Customer owns secrets, model provider keys, license configuration, storage buckets, and auth provider.
- ChipLoop provides Docker images, Compose/Helm templates, migrations, and configuration contracts.

Use this when specs/artifacts cannot leave the customer environment.

## Configuration Contracts

### Tool Profile

Tool profiles map abstract tool names used by agents to concrete executables and environment variables.

Examples:
- SaaS default: `backend/config/tool_profiles/chiploop_saas_default.json`
- Private runner example: `backend/config/tool_profiles/customer_private_runner.example.json`

Set with:

```bash
CHIPLOOP_TOOL_PROFILE_PATH=/etc/chiploop/tool_profile.json
```

### Model Profile

Model profiles map ChipLoop agent roles to a provider and model names. This is required for model-agnostic private deployments.

Hosted SaaS defaults to OpenAI with `gpt-5.5`. If a customer brings their own provider, API keys, or model deployments, the customer is responsible for managing those keys, provider contracts, and model licensing.

Profiles can route by capability and by agent. For example, documentation agents can use Claude while RTL/spec generation stays on GPT 5.5:

```json
{
  "provider": "openai",
  "routing": {
    "rtl_generation": {"model": "gpt-5.5"},
    "doc_generation": {"provider": "anthropic", "model": "claude-sonnet-4-5"},
    "summarizer": {"model": "gpt-5.4"}
  },
  "agents": {
    "Digital RTL Agent": {"model": "gpt-5.5"},
    "Digital Architecture Documentation Agent": {"provider": "anthropic", "model": "claude-sonnet-4-5"}
  }
}
```

Example provider types:
- `openai`
- `azure_openai`
- `aws_bedrock`
- `anthropic`
- `vertex_ai`
- `openai_compatible`

Recommended environment variable:

```bash
CHIPLOOP_MODEL_PROFILE_PATH=/etc/chiploop/model_profile.json
```

### Storage Provider

Supabase remains the default. Private deployments should support storage adapters:

- `supabase`
- `s3`
- `azure_blob`
- `gcs`
- `local_fs`
- `minio`

Recommended environment variables:

```bash
CHIPLOOP_STORAGE_PROVIDER=s3
CHIPLOOP_STORAGE_BUCKET=chiploop-artifacts
CHIPLOOP_STORAGE_PREFIX=prod
```

### Auth Provider

Supabase Auth remains the default. Private deployments should support:

- `supabase_auth`
- `oidc`
- `azure_ad`
- `okta`
- `auth0`
- `local_jwt`

Recommended environment variables:

```bash
CHIPLOOP_AUTH_PROVIDER=oidc
CHIPLOOP_OIDC_ISSUER=https://login.microsoftonline.com/<tenant>/v2.0
CHIPLOOP_OIDC_CLIENT_ID=<client-id>
```

## License Handling

ChipLoop containers must not package commercial license files.

For hybrid private runner:

```bash
SNPSLMD_LICENSE_FILE=27000@license-server
CDS_LIC_FILE=5280@license-server
LM_LICENSE_FILE=27000@license-server
```

For full private deployment, the same variables are managed by the customer deployment environment. Tool paths and license variables should be visible only inside the private runner/backend containers.

## Recommended Rollout

1. Keep hosted SaaS on `chiploop_saas_default`.
2. Package and test hybrid runner with open-source tools first.
3. Add customer commercial tool profile for Synopsys/Cadence.
4. Add read-only UI display for the active tool/model profile used by each run.
5. Add full private Compose/Helm deployment after hybrid runner is stable.
