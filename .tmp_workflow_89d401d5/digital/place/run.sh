#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Placement Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/89d401d5-3193-4ed9-991f-efda69c754f9/8fe6c416-1ab8-45e7-b3ac-dade936281f4/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_89d401d5-3193-4ed9-991f-efda69c754f9 --override-config RUN_LINTER=False --to OpenROAD.DetailedPlacement place/config.json'


