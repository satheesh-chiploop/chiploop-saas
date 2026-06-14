#!/usr/bin/env bash
set -euo pipefail
echo "ChipLoop Analog GDS Generation Agent"
echo "SPICE=/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e75e64c3-66e3-423d-8ea2-9c56a222afcc/58c6a884-0b71-405a-9c37-f42f282a7c0f/digital/analog/gds/temp_sensor_adc_model.sp"
echo "TOP=temp_sensor_adc_model"
echo "PDK=sky130A"
echo "PDK_ROOT_HOST=/root/chiploop-backend/backend/pdk"
echo "ALIGN_PDK_HOST="
docker run --rm -v /root/chiploop-backend/backend/pdk:/pdk -v /root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/e75e64c3-66e3-423d-8ea2-9c56a222afcc/58c6a884-0b71-405a-9c37-f42f282a7c0f/digital/analog/gds:/work -w /work ghcr.io/efabless/openlane2:2.4.0.dev1 magic -dnull -noconsole -T /pdk/sky130A/libs.tech/magic/sky130A.tech /work/magic_import_spice.tcl
