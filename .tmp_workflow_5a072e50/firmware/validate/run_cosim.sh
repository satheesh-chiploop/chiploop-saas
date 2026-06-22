#!/usr/bin/env bash
set -euo pipefail

RTL_TOP=${RTL_TOP:-<RTL_TOP>}
RTL_DIR=${RTL_DIR:-<RTL_DIR>}
FILELIST=${FILELIST:-<FILELIST>}
FW_DIR=${FW_DIR:-.}
COSIM_OUT=${COSIM_OUT:-firmware/validate/out}
PYTEST_ARGS=${PYTEST_ARGS:-"-q"}
VERILATOR_BUILD_MD="firmware/validate/verilator_build.md"

mkdir -p "${COSIM_OUT}"

if [[ -f "${VERILATOR_BUILD_MD}" ]]; then
  echo "Using preferred Verilator build steps from ${VERILATOR_BUILD_MD}"
  if command -v python3 >/dev/null 2>&1; then
    python3 - <<'PY'
from pathlib import Path
p = Path("firmware/validate/verilator_build.md")
print(p.read_text())
PY
  fi
fi

if [[ -n "${RTL_DIR}" && -d "${RTL_DIR}" ]]; then
  :
fi

echo "Building firmware (if applicable)"
if [[ -f "${FW_DIR}/Cargo.toml" ]]; then
  cargo build --manifest-path "${FW_DIR}/Cargo.toml" 2>&1 | tee "${COSIM_OUT}/cargo_build.log"
else
  echo "No Cargo.toml found at ${FW_DIR}/Cargo.toml; skipping firmware build" | tee "${COSIM_OUT}/cargo_build.log"
fi

if [[ -f "${VERILATOR_BUILD_MD}" ]]; then
  echo "Verilator build instructions detected; caller should follow firmware/validate/verilator_build.md"
else
  echo "Building RTL simulation with Verilator"
  verilator -cc --exe --build --top-module "${RTL_TOP}" -Mdir "${COSIM_OUT}/verilator_obj" -CFLAGS "-O2" -f "${FILELIST}" 2>&1 | tee "${COSIM_OUT}/verilator_build.log"
fi

echo "Running cocotb via pytest"
pytest ${PYTEST_ARGS} firmware/validate --junitxml="${COSIM_OUT}/junit.xml" 2>&1 | tee "${COSIM_OUT}/pytest.log"

echo "Co-simulation completed successfully"
