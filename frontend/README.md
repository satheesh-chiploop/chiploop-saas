# ChipLoop Frontend Playbook

This frontend is the ChipLoop SaaS UI. It is a Next.js app deployed on Vercel and backed by the ChipLoop backend API, which is deployed separately. Supabase provides browser authentication and, in hosted SaaS mode, workflow/product data and artifact storage.

## Local Development

```bash
npm install
npm run dev
```

Open `http://localhost:3000`.

The browser API client lives in `lib/apiClient.ts`. It calls relative `/api/*` routes and attaches the current Supabase session bearer token when available. Vercel or local rewrites should forward `/api/*` to the backend.

## Main User Surfaces

- `/apps`: guided single-workflow Apps grouped by loop.
- `/products`: reference journeys and saved product journeys.
- `/products/[productId]`: editable product stage sequence, stage settings, product run dashboard, and per-stage run history.
- `/workflow`: Studio canvas for custom workflows, planners, workflow composition, and private agents.
- `/help`: in-app Playbook plus Ask ChipLoop Help.
- `/settings/*`: plan, usage, API keys, integrations, and deployment diagnostics.
- `/marketplace` and `/admin/marketplace`: agent marketplace surfaces.

## Current App Catalog

Digital Apps include Arch2RTL, Spec2RTL Check, Arch2Synthesis, Arch2Tapeout, DQA, Verify, Smoke, and Integrate.

System Apps include System Architecture Explorer, Cache Tuning, ISA Compare, Memory Bottleneck, CPU Model, Architecture-to-RTL Delivery, System RTL, System Synthesis, System DQA, System Sim, System Firmware, System PD, System Software, System Software Validation, and Product App Builder.

Embedded Apps include HAL, Driver, Boot, Diagnostics, Log Analyzer, Validate, and Embedded Run.

Validation Apps include Validation Run, Validation Plan, Bench Setup, Preflight, and Validation Insights. Analog Apps include spec, netlist, model, validate-model, correlate, iterate, abstracts, and run flows.

## Products and Reference Journeys

Products are saved journey configurations built from existing Apps. A product stage is a configured use of an existing App in an ordered sequence, not a new App definition.

The backend currently provides these reference journeys:

- PWM Fan Controller.
- UART Packet Engine.
- Image DMA Pipeline.
- Soft Digital IP Product.
- Temperature Monitor SoC.

The Product detail page supports:

- Add Stage from the existing App catalog.
- Drag/drop or Move Up / Move Down sequence editing.
- Required, Recommended, or Optional stage classification.
- Remove non-required stages.
- Dynamic stage settings from `/products/stage-schemas`.
- Sequence guidance before run, including RTL, firmware, software, validation, and product-app handoff checks.
- Run Product execution through backend product orchestration.

Current dynamic digital controls include MBIST insertion, MBIST algorithm selection, Spec2RTL conformance, synthesis closure, signoff closure, DRC/LVS/fill/LEC, and tapeout effort.

## Backend API Boundary

The frontend depends on these backend surfaces:

- App run endpoints such as `/apps/arch2rtl/run`, `/apps/verify/run`, `/apps/arch2synthesis/run`, `/apps/arch2tapeout/run`, `/apps/system/*/run`, `/apps/embedded/*/run`, and `/apps/validation/run`.
- Artifact endpoints: `/list_artifacts/{workflow_id}`, `/download_artifacts/{workflow_id}/{rel_path}`, `/workflow/{workflow_id}/download_zip`, and `/apps/dashboard/artifact/{workflow_id}`.
- Product endpoints: `/products/reference-journeys`, `/products/stage-schemas`, `/products`, `/products/{product_id}`, `/products/{product_id}/run`, and `/products/{product_id}/runs`.
- Help endpoints: `/help/ask` and `/help/catalog`.
- Studio/planner endpoints: `/plan_workflow`, `/analyze_spec`, `/plan_agent`, `/save_custom_agent`, `/save_custom_workflow`, `/build_workflow`, and workflow composition routes.
- Settings, billing, API key, marketplace, deployment, and integration routes exposed through backend browser routes.

## Playbook Content

The in-app Playbook source is `lib/helpContent.ts`. The backend Ask Help corpus is `backend/help_center/content.py`. Keep both updated when product behavior, app names, reference journey sequences, dashboards, or interpretation guidance changes.

## Validation

Useful local checks:

```bash
npm run lint
.\node_modules\.bin\tsc.cmd --noEmit --project tsconfig.json
```

At the current repo snapshot, full TypeScript checking may report pre-existing errors outside the Product page. When touching Product or Playbook files, use targeted review plus backend tests for the corresponding API/help content.
