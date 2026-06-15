#!/usr/bin/env bash
set -euo pipefail

echo "== ChipLoop: Digital Synthesis Agent =="
echo "PDK_VARIANT=sky130A"
echo "OPENLANE_IMAGE=ghcr.io/efabless/openlane2:2.4.0.dev1"
echo "WORKDIR=/work"
echo "MACRO_LIB_COUNT=1"
echo

docker run --rm \
  -v "/root/chiploop-backend/backend/pdk:/pdk" \
  -v "/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/89d401d5-3193-4ed9-991f-efda69c754f9/8fe6c416-1ab8-45e7-b3ac-dade936281f4/digital/digital/synth:/work" \
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
    openlane --pdk sky130A --run-tag System_PD_89d401d5-3193-4ed9-991f-efda69c754f9 --flow Classic --override-config RUN_LINTER=False --to OpenROAD.STAPrePNR config.json

    # Patch the synthesized design with explicit Liberty blackbox load if macro libs exist
    if [ -n "read_liberty -lib macro_libs/temp_sensor_adc_model.lib;" ]; then
      echo "Applying Liberty blackbox integration post-synthesis..."
      echo "read_liberty -lib macro_libs/temp_sensor_adc_model.lib;" > /tmp/chiploop_macro_libs.ys
      cat /tmp/chiploop_macro_libs.ys
    fi
  '

echo
echo "Done. Inspect /work/runs/System_PD_89d401d5-3193-4ed9-991f-efda69c754f9 or latest run folder under /work/runs/"
