#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "${SCRIPT_DIR}/../.." && pwd)
cd "${REPO_ROOT}"

RTL_TOP=${RTL_TOP:-<RTL_TOP>}
RTL_DIR=${RTL_DIR:-<RTL_DIR>}
FILELIST=${FILELIST:-<FILELIST>}

OUT_DIR="firmware/validate"
RTL_BUILD_DIR="${OUT_DIR}/rtl_build"
LOG_FILE="${OUT_DIR}/cosim.log"
JUNIT_FILE="${OUT_DIR}/junit.xml"

mkdir -p "${OUT_DIR}" "${RTL_BUILD_DIR}"

{
  echo "[cosim] RTL_TOP=${RTL_TOP}"
  echo "[cosim] RTL_DIR=${RTL_DIR}"
  echo "[cosim] FILELIST=${FILELIST}"
  echo "[cosim] repo_root=${REPO_ROOT}"
  echo "[cosim] out_dir=${OUT_DIR}"
} | tee "${LOG_FILE}"

if [[ -f "${OUT_DIR}/verilator_build.md" ]]; then
  echo "[cosim] Found firmware/validate/verilator_build.md; using documented build guidance." | tee -a "${LOG_FILE}"
fi

if command -v verilator >/dev/null 2>&1; then
  echo "[cosim] Building RTL simulation with Verilator..." | tee -a "${LOG_FILE}"
else
  echo "[cosim] ERROR: verilator not found on PATH" | tee -a "${LOG_FILE}"
  exit 1
fi

if [[ ! -f "${FILELIST}" && "${FILELIST}" != "<FILELIST>" ]]; then
  echo "[cosim] Using provided file list: ${FILELIST}" | tee -a "${LOG_FILE}"
fi

VERILATOR_CMD=(verilator -Wall --cc --exe --build -Mdir "${RTL_BUILD_DIR}" --top-module "${RTL_TOP}")
if [[ "${FILELIST}" != "<FILELIST>" ]]; then
  VERILATOR_CMD+=(-f "${FILELIST}")
fi
if [[ -n "${RTL_DIR}" && "${RTL_DIR}" != "<RTL_DIR>" ]]; then
  VERILATOR_CMD+=(-I"${RTL_DIR}")
fi

printf '[cosim] cmd:' | tee -a "${LOG_FILE}"
printf ' %q' "${VERILATOR_CMD[@]}" | tee -a "${LOG_FILE}"
printf '\n' | tee -a "${LOG_FILE}"

"${VERILATOR_CMD[@]}" 2>&1 | tee -a "${LOG_FILE}"

if [[ -f "firmware/Cargo.toml" ]]; then
  echo "[cosim] Building firmware with cargo..." | tee -a "${LOG_FILE}"
  cargo build --manifest-path firmware/Cargo.toml 2>&1 | tee -a "${LOG_FILE}"
else
  echo "[cosim] WARNING: firmware/Cargo.toml not found; skipping firmware build." | tee -a "${LOG_FILE}"
fi

echo "[cosim] Running cocotb tests via pytest..." | tee -a "${LOG_FILE}"
PYTEST_CMD=(pytest -q "${OUT_DIR}" --junitxml="${JUNIT_FILE}")
printf '[cosim] cmd:' | tee -a "${LOG_FILE}"
printf ' %q' "${PYTEST_CMD[@]}" | tee -a "${LOG_FILE}"
printf '\n' | tee -a "${LOG_FILE}"

"${PYTEST_CMD[@]}" 2>&1 | tee -a "${LOG_FILE}"

if [[ -f "firmware/Cargo.toml" ]]; then
  echo "[cosim] Optional firmware coverage collection..." | tee -a "${LOG_FILE}"
  if command -v cargo >/dev/null 2>&1 && cargo help llvm-cov >/dev/null 2>&1; then
    cargo llvm-cov --manifest-path firmware/Cargo.toml --lcov --output-path "${OUT_DIR}/fw_coverage.lcov" 2>&1 | tee -a "${LOG_FILE}"
  else
    echo "[cosim] WARNING: cargo llvm-cov not available; skipping FW coverage." | tee -a "${LOG_FILE}"
  fi
fi

echo "[cosim] Done." | tee -a "${LOG_FILE}"
