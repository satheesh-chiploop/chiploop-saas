#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital CTS Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"

export OPENLANE_NUM_CORES=2

docker run --rm   -v "/root/chiploop-backend/backend/pdk":/pdk   -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/7ef40733-5be0-4054-8943-441591ec8735/832e1f5a-553d-4e98-be44-98e4f24c4ae9/digital/arch2tapeout/digital/run_work":/work   -e PDK=sky130A   -e PDK_ROOT=/pdk   ghcr.io/efabless/openlane2:2.4.0.dev1   bash -lc 'set -e; cd /work && openlane --flow Classic --run-tag Digital_Arch2Tapeout_7ef40733-5be0-4054-8943-441591ec8735 --override-config RUN_LINTER=False --to OpenROAD.CTS cts/config.json'

