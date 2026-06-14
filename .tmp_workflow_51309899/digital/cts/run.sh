#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital CTS Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/51309899-ca8a-4d6b-9dea-fe920ed5245a/dcd843f9-fbf5-4346-87d3-d80a96d61c3d/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_51309899-ca8a-4d6b-9dea-fe920ed5245a --override-config RUN_LINTER=False --to OpenROAD.CTS cts/config.json'

