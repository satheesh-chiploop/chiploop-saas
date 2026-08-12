#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Placement Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/dd095a60-e45f-44c3-beb0-943e030b19e3/ff5167b1-75d5-4b82-8bf2-b2321c18cdb9/digital/arch2tapeout/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && timeout --foreground --kill-after=30s 1500s openlane --flow Classic --run-tag Digital_Arch2Tapeout_dd095a60-e45f-44c3-beb0-943e030b19e3 --override-config RUN_LINTER=False --to OpenROAD.DetailedPlacement place/config.json'


