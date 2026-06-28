#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Synthesis Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"
echo "MACRO_LIB_COUNT=0"
echo

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk:/pdk" \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/41674526-178c-4697-8807-decc13101353/ba0e4323-1a09-4cd3-a062-2e5e5913a435/digital/arch2synthesis/digital/synth:/work" \
  -e PDK_ROOT=/pdk \
  -e PDK=sky130A \
  -e OPENLANE_NUM_CORES=2 \
  "ghcr.io/efabless/openlane2:2.4.0.dev1" \
  bash -lc '
    set -e
    echo "PDK listing:"
    ls -la /pdk | head -n 50
    test -f /pdk/sky130A/libs.tech/openlane/config.tcl
    cd /work

    if [ -d macro_libs ]; then
      echo "Using macro Liberty blackbox libraries:"
      ls -la macro_libs || true
    fi

    # Run OpenLane synthesis through pre-PnR STA. This keeps the Synth app
    # lightweight while producing real OpenSTA/OpenROAD WNS/TNS metrics.
    openlane --pdk sky130A --run-tag Digital_Arch2Synthesis_41674526-178c-4697-8807-decc13101353 --flow Classic --override-config RUN_LINTER=False --to OpenROAD.STAPrePNR config.json

    # Patch the synthesized design with explicit Liberty blackbox load if macro libs exist
    if [ -n "" ]; then
      echo "Applying Liberty blackbox integration post-synthesis..."
      echo "" > /tmp/chiploop_macro_libs.ys
      cat /tmp/chiploop_macro_libs.ys
    fi
  '

echo
echo "Done. Inspect /work/runs/Digital_Arch2Synthesis_41674526-178c-4697-8807-decc13101353 or latest run folder under /work/runs/"
