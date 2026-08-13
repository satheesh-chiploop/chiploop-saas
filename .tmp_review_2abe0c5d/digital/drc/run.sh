#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital DRC Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk":/pdk \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/2abe0c5d-7ac4-43fe-8031-ae931b35b29f/b4a2d3ee-d6f5-41d7-8ee3-2683e506f826/digital/arch2tapeout/digital/run_work":/work \
  -e PDK=sky130A \
  -e PDK_ROOT=/pdk \
  ghcr.io/efabless/openlane2:2.4.0.dev1 \
  bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag Digital_Arch2Tapeout_2abe0c5d-7ac4-43fe-8031-ae931b35b29f --override-config RUN_LINTER=False --to KLayout.DRC drc/config.json'
