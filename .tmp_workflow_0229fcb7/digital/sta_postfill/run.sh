#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital STA PostFill Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/0229fcb7-ede5-4185-95d5-2deefa86134d/0ac7a25b-9f47-49dd-8c66-c437397a9518/digital/arch2tapeout/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag Digital_Arch2Tapeout_0229fcb7-ede5-4185-95d5-2deefa86134d --override-config RUN_LINTER=False --to OpenROAD.STAPostPNR sta_postfill/config.json'
