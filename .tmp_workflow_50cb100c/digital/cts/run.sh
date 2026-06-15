#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital CTS Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/50cb100c-b2cd-4c0d-9eee-0c8b7ddc5f38/981a3b76-c90b-4b3b-ad51-ac5cc8eacaf9/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_50cb100c-b2cd-4c0d-9eee-0c8b7ddc5f38 --override-config RUN_LINTER=False --to OpenROAD.CTS cts/config.json'

