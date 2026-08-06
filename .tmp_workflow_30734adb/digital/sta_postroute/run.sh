#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital STA PostRoute Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/30734adb-33b9-4000-8b0e-a911961bac0f/a3d869e5-ee6f-4838-9460-66c7ab5ff8f1/digital/arch2tapeout/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag Digital_Arch2Tapeout_30734adb-33b9-4000-8b0e-a911961bac0f --override-config RUN_LINTER=False --to OpenROAD.STAPostPNR sta_postroute/config.json'
