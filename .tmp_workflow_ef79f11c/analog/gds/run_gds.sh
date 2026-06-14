#!/usr/bin/env bash
set -euo pipefail
echo "ChipLoop Analog GDS Generation Agent"
echo "SPICE=/root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/ef79f11c-7fde-4de5-91b0-6151d9f0d65a/3b3d5d21-0161-4fa4-b691-4699c2f9ae10/digital/analog/gds/temp_sensor_adc_model.sp"
echo "TOP=temp_sensor_adc_model"
echo "PDK=sky130A"
echo "PDK_ROOT_HOST=/root/chiploop-backend/backend/pdk"
echo "ALIGN_PDK_HOST="
docker run --rm -v /root/chiploop-backend/backend/pdk:/pdk -v /root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/ef79f11c-7fde-4de5-91b0-6151d9f0d65a/3b3d5d21-0161-4fa4-b691-4699c2f9ae10/digital/analog/gds:/work -w /work ghcr.io/efabless/openlane2:2.4.0.dev1 magic -dnull -noconsole -T /pdk/sky130A/libs.tech/magic/sky130A.tech /work/magic_import_spice.tcl
