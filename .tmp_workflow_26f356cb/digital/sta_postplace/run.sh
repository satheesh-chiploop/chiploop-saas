#!/usr/bin/env bash
set -euo pipefail
export OPENLANE_NUM_CORES=2
docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/26f356cb-6d29-43be-a1da-649876540ea6/6d479abf-c006-4bf3-b6cb-21bcf6d57fc4/digital/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag System_PD_26f356cb-6d29-43be-a1da-649876540ea6 --override-config RUN_LINTER=False --to OpenROAD.STAMidPNR place/config.json'
