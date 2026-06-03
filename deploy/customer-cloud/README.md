# ChipLoop Customer Cloud Deployment

This package is for customers deploying ChipLoop into their Azure, AWS, or GCP environment.

## Customer Owns

- Cloud account, VPC/VNet, IAM, DNS, TLS, secrets, and monitoring.
- Backend, database/storage, EDA tools, licenses, and model provider access.
- Optional frontend hosting when the customer requires a fully isolated experience.

## Configure

1. Copy `.env.customer-cloud.example` to `.env.customer-cloud`.
2. Mount a strict tool profile at `/etc/chiploop/tool_profile.json`.
3. Mount a model profile for Azure OpenAI, AWS Bedrock, OpenAI, Anthropic, or an OpenAI-compatible gateway.
4. Configure customer database/storage/auth secrets.
5. Start the deployment and run the healthcheck.

For PostgreSQL plus OIDC, use the backend-platform frontend build:

- `CHIPLOOP_FRONTEND_PLATFORM_PROVIDER=backend_platform_api`
- `NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER=backend`

Route browser `/api/*` traffic to the backend so OIDC session cookies remain same-origin.

```bash
docker compose -f docker-compose.customer-cloud.yml up -d
docker compose -f docker-compose.customer-cloud.yml exec backend python -m chiploop_sdk.runner_healthcheck
docker compose -f docker-compose.customer-cloud.yml exec backend python -m chiploop_sdk.support_bundle
```

## Security

- Use cloud secret managers for API keys and license variables.
- Keep `strict_tool_profile` enabled.
- Use `customer_cloud_storage`, `private_storage`, or `full_private` artifact policy when design artifacts must not leave the customer account.
