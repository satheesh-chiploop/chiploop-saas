#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Floorplan Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/c2f0de28-0c09-449a-8d62-5ce2fe39e3fd/9b7a99fa-09e4-4930-9752-55bd40be251b/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_c2f0de28-0c09-449a-8d62-5ce2fe39e3fd --override-config RUN_LINTER=False --to OpenROAD.Floorplan floorplan/config.json'


