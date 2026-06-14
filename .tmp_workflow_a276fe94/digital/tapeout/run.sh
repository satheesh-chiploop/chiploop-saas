#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Tapeout Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/a276fe94-5253-47b7-8ecc-34ee2c78817c/3e47c6ea-bdee-4a3a-acfe-3193056b82c1/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_a276fe94-5253-47b7-8ecc-34ee2c78817c --override-config RUN_LINTER=False --to KLayout.StreamOut tapeout/config.json'

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/a276fe94-5253-47b7-8ecc-34ee2c78817c/3e47c6ea-bdee-4a3a-acfe-3193056b82c1/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_a276fe94-5253-47b7-8ecc-34ee2c78817c --override-config RUN_LINTER=False --to Magic.StreamOut tapeout/config.json || true'

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/a276fe94-5253-47b7-8ecc-34ee2c78817c/3e47c6ea-bdee-4a3a-acfe-3193056b82c1/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_a276fe94-5253-47b7-8ecc-34ee2c78817c --override-config RUN_LINTER=False --to KLayout.XOR tapeout/config.json || true'
