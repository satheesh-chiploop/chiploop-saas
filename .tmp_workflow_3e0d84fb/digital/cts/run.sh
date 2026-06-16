#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital CTS Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/3e0d84fb-1bc2-4064-a8dc-9ac94ff7a1fc/e297e8a2-39e1-4a30-882c-43b9cde8dfbe/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_3e0d84fb-1bc2-4064-a8dc-9ac94ff7a1fc --override-config RUN_LINTER=False --to OpenROAD.CTS cts/config.json'

