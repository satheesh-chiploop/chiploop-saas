# Physical AI reference-journey deployment

The PMSM reference journey uses Supabase as the source of truth for the model
catalog, workflow/run state, HEM state, artifact index, and artifact bodies in
Storage. DigitalOcean local files are an execution cache only.

## 1. Apply the additive Supabase migration

In the Supabase SQL editor for the production project, run:

`backend/supabase/migrations/phase_20260803_physical_ai_source_of_truth.sql`

Do this before deploying the backend. The updated API intentionally returns 503
when the governed `physical_ai_models` catalog is unavailable.

## 2. Configure the DigitalOcean backend

Required for equation mode:

```text
SUPABASE_URL=...
SUPABASE_SERVICE_ROLE_KEY=...
ARTIFACT_BUCKET_NAME=artifacts
```

Required for NVIDIA Nemotron agent mode:

```text
NVIDIA_API_KEY=...
NVIDIA_NIM_BASE_URL=https://integrate.api.nvidia.com/v1
NVIDIA_NEMOTRON_MODEL=nvidia/nemotron-3-nano-30b-a3b
```

PhysicsNeMo worker variables can remain unset during PMSM equation mode.

## 3. Run the read-only preflight

From the backend directory on DigitalOcean:

```text
python scripts/physical_ai_preflight.py
```

To include the deployed authenticated API check, also set `CHIPLOOP_API_URL`
and a short-lived user `CHIPLOOP_ACCESS_TOKEN`. The script never prints tokens.

## 4. Run the cloud reference journey

Use Physical AI Studio with HEM enabled. Confirm Supabase contains the parent
workflow/run, the HEM run/events, and child workflows for FPGA exploration,
bitstream, firmware, software, validation, and product demo. Confirm generated
files are in the `artifacts` bucket and indexed by `workflows.artifacts`.

The run must stop at `hardware_validation_plan.json`. FPGA programming, gate
driver enable, and motor energization require explicit operator approval and are
not part of automatic cloud validation.
