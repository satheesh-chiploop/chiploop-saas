#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Placement Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e6ffce8d-17d7-4511-aae3-34c953406829/aea4e7a4-8d37-486d-86c2-cd3dcc00ee22/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_e6ffce8d-17d7-4511-aae3-34c953406829 --override-config RUN_LINTER=False --to OpenROAD.DetailedPlacement place/config.json'


