# Full Private Deployment

This package is for customers who host ChipLoop entirely inside their environment.

## Customer Owns

- Frontend hosting.
- Backend/runtime.
- Database and storage.
- Authentication provider.
- Model provider keys.
- EDA tools, PDKs, licenses, and internal repositories.

## Install

```bash
cp .env.private.example .env.private
cp ../../backend/config/tool_profiles/customer_private_runner.example.json tool_profile.json
cp ../../backend/config/model_profiles/customer_azure_openai.example.json model_profile.json
docker compose -f docker-compose.private.yml up -d
```

## Adapter Requirements

Private deployments should configure:

- `CHIPLOOP_STORAGE_PROVIDER`
- `CHIPLOOP_AUTH_PROVIDER`
- `CHIPLOOP_MODEL_PROFILE_PATH`
- `CHIPLOOP_TOOL_PROFILE_PATH`

Supabase can still be used by private deployments, but it should be treated as one adapter option rather than a hard requirement.

