#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Tapeout Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dda5224a-c8b1-449c-bf86-ea84c3c162ed/0fa4930c-0d34-4eaa-8538-5cafb6bc569d/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_dda5224a-c8b1-449c-bf86-ea84c3c162ed --override-config RUN_LINTER=False --to KLayout.StreamOut tapeout/config.json'

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dda5224a-c8b1-449c-bf86-ea84c3c162ed/0fa4930c-0d34-4eaa-8538-5cafb6bc569d/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_dda5224a-c8b1-449c-bf86-ea84c3c162ed --override-config RUN_LINTER=False --to Magic.StreamOut tapeout/config.json || true'

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dda5224a-c8b1-449c-bf86-ea84c3c162ed/0fa4930c-0d34-4eaa-8538-5cafb6bc569d/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_dda5224a-c8b1-449c-bf86-ea84c3c162ed --override-config RUN_LINTER=False --to KLayout.XOR tapeout/config.json || true'
