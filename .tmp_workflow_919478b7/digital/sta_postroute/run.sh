#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital STA PostRoute Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/919478b7-46be-40fa-8ff0-688455fbfa56/bd979697-7a54-4d39-b158-657e0fb25348/digital/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_919478b7-46be-40fa-8ff0-688455fbfa56 --override-config RUN_LINTER=False --to OpenROAD.STAPostPNR sta_postroute/config.json'
