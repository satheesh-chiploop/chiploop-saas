#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VALIDATE_DIR="${SCRIPT_DIR}"
COSIM_OUT_DIR="${COSIM_OUT_DIR:-${VALIDATE_DIR}/cosim_out}"
FW_BUILD_DIR="${FW_BUILD_DIR:-${VALIDATE_DIR}/fw_build}"
RTL_TOP="${RTL_TOP:-<RTL_TOP>}"
RTL_DIR="${RTL_DIR:-<RTL_DIR>}"
FILELIST="${FILELIST:-<FILELIST>}"
PYTEST_ARGS="${PYTEST_ARGS:-}"

mkdir -p "${COSIM_OUT_DIR}"
mkdir -p "${FW_BUILD_DIR}"

VERILATOR_BUILD_MD="${VALIDATE_DIR}/verilator_build.md"
VERILATOR_BUILD_SH="${VALIDATE_DIR}/verilator_build.sh"

if [[ -f "${VERILATOR_BUILD_SH}" ]]; then
  bash "${VERILATOR_BUILD_SH}"
elif [[ -f "${VERILATOR_BUILD_MD}" ]]; then
  echo "INFO: Found ${VERILATOR_BUILD_MD}; please follow its build instructions before running cocotb."
  if [[ "${RTL_TOP}" == "<RTL_TOP>" || "${RTL_DIR}" == "<RTL_DIR>" || "${FILELIST}" == "<FILELIST>" ]]; then
    echo "ERROR: RTL_TOP, RTL_DIR, and FILELIST must be set for the RTL build." >&2
    exit 1
  fi
  echo "INFO: Generic Verilator build placeholder:"
  echo "  verilator --top-module \"${RTL_TOP}\" -Mdir \"${COSIM_OUT_DIR}/verilator_build\" -f \"${FILELIST}\""
else
  if [[ "${RTL_TOP}" == "<RTL_TOP>" || "${RTL_DIR}" == "<RTL_DIR>" || "${FILELIST}" == "<FILELIST>" ]]; then
    echo "ERROR: RTL_TOP, RTL_DIR, and FILELIST must be set for the RTL build." >&2
    exit 1
  fi
  echo "INFO: No verilator_build.md found; using generic build placeholder."
  echo "INFO: Generic Verilator build placeholder:"
  echo "  verilator --top-module \"${RTL_TOP}\" -Mdir \"${COSIM_OUT_DIR}/verilator_build\" -f \"${FILELIST}\""
fi

if [[ -f "${VALIDATE_DIR}/firmware_build.sh" ]]; then
  bash "${VALIDATE_DIR}/firmware_build.sh"
elif [[ -f "${VALIDATE_DIR}/build_fw.sh" ]]; then
  bash "${VALIDATE_DIR}/build_fw.sh"
else
  echo "INFO: No firmware build script found; skipping firmware build."
fi

export PYTHONUNBUFFERED=1
export COCOTB_RESULTS_FILE="${COSIM_OUT_DIR}/cocotb_results.xml"

pytest -q "${VALIDATE_DIR}" ${PYTEST_ARGS} --junitxml="${COSIM_OUT_DIR}/junit.xml"
