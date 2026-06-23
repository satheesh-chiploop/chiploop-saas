#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BUILD_DIR="${BUILD_DIR:-${SCRIPT_DIR}/build}"
LOG_DIR="${SCRIPT_DIR}/logs"
RTL_TOP="${RTL_TOP:-<RTL_TOP>}"
RTL_DIR="${RTL_DIR:-<RTL_DIR>}"
FILELIST="${FILELIST:-<FILELIST>}"
FW_MANIFEST="${FW_MANIFEST:-${ROOT_DIR}/Cargo.toml}"
COCOTB_TEST_DIR="${COCOTB_TEST_DIR:-${SCRIPT_DIR}}"
COCOTB_TEST_MODULES="${COCOTB_TEST_MODULES:-}"
VERILATOR_BUILD_MD="${SCRIPT_DIR}/verilator_build.md"

mkdir -p "${BUILD_DIR}" "${LOG_DIR}"

if [[ -f "${VERILATOR_BUILD_MD}" ]]; then
  echo "Using build collateral from ${VERILATOR_BUILD_MD}"
  sed -n '1,240p' "${VERILATOR_BUILD_MD}"
fi

if [[ "${RTL_TOP}" == "<RTL_TOP>" || "${RTL_DIR}" == "<RTL_DIR>" || "${FILELIST}" == "<FILELIST>" ]]; then
  echo "ERROR: Set RTL_TOP, RTL_DIR, and FILELIST environment overrides." >&2
  exit 1
fi

echo "Building RTL simulation with Verilator..."
verilator \
  --cc \
  --exe \
  --build \
  --top-module "${RTL_TOP}" \
  -Mdir "${BUILD_DIR}/verilator" \
  --trace \
  --coverage \
  -f "${FILELIST}" \
  2>&1 | tee "${LOG_DIR}/verilator_build.log"

if [[ -f "${FW_MANIFEST}" ]]; then
  echo "Building Rust firmware..."
  cargo build --manifest-path "${FW_MANIFEST}" --release \
    2>&1 | tee "${LOG_DIR}/cargo_build.log"
fi

PYTEST_ARGS=(
  -q
  --junitxml="${SCRIPT_DIR}/junit.xml"
  --log-cli-level=INFO
)

if [[ -n "${COCOTB_TEST_MODULES}" ]]; then
  export COCOTB_TEST_MODULES
fi

if [[ -d "${COCOTB_TEST_DIR}" ]]; then
  PYTEST_ARGS+=("${COCOTB_TEST_DIR}")
else
  PYTEST_ARGS+=("${SCRIPT_DIR}")
fi

echo "Running cocotb via pytest..."
pytest "${PYTEST_ARGS[@]}" \
  2>&1 | tee "${LOG_DIR}/pytest_cocotb.log"

echo "Co-simulation completed successfully."
