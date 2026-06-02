# Hybrid Private Runner

This package is for customers who use ChipLoop hosted SaaS but execute tools inside their private network.

## Files

- `docker-compose.runner.yml`: runner-only deployment.
- `.env.runner.example`: environment variables to copy to `.env.runner`.
- `tool_profile.json`: copy from `backend/config/tool_profiles/customer_private_runner.example.json` and edit for customer tools.
- `model_profile.json`: copy from `backend/config/model_profiles/customer_azure_openai.example.json` or another provider profile.

## Install

```bash
cp .env.runner.example .env.runner
cp ../../backend/config/tool_profiles/customer_private_runner.example.json tool_profile.json
cp ../../backend/config/model_profiles/customer_azure_openai.example.json model_profile.json
docker compose -f docker-compose.runner.yml up -d
```

## Validation

Inside the runner container, verify:

```bash
which verilator
which yosys
which sby
which dc_shell || true
which genus || true
python -c "print('chiploop runner python ok')"
```

## Security

- Do not put license files in the image.
- Mount customer EDA tools read-only.
- Use `summary_only` or `metadata_only` artifact policy when full artifacts cannot leave the customer network.

