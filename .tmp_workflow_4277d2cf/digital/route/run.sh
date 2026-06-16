#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Route Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/4277d2cf-725a-4295-96ed-62c59855efb8/f4c7b80f-2041-4bb7-bc2d-6985967fe443/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_4277d2cf-725a-4295-96ed-62c59855efb8 --override-config RUN_LINTER=False --to OpenROAD.STAPostPNR route/config.json'
