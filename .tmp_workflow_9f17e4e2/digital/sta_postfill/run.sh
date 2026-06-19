#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital STA PostFill Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/9f17e4e2-4c7c-47d3-a9ba-4d09c2f00169/fb1e0dee-ceb5-417a-900a-47409d974a5c/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_9f17e4e2-4c7c-47d3-a9ba-4d09c2f00169 --override-config RUN_LINTER=False --to OpenROAD.STAPostPNR sta_postfill/config.json'
