#!/usr/bin/env bash
set -euo pipefail
export OPENLANE_NUM_CORES=2
docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/43c71124-316e-411a-ba15-1e794fa059b8/de6a80c1-7843-495a-a19e-f72bbbbc2fce/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_43c71124-316e-411a-ba15-1e794fa059b8 --override-config RUN_LINTER=False --to OpenROAD.STAMidPNR place/config.json'
