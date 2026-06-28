<!-- ASSUMPTION: RTL_TOP, RTL_DIR, and FILELIST are provided by the environment or the caller when running the co-simulation flow. -->
<!-- ASSUMPTION: A Verilator build flow exists or is described in firmware/validate/verilator_build.md; if present, this flow should be followed. -->
<!-- ASSUMPTION: The firmware build is optional and only required if the DUT behavior depends on generated firmware artifacts. -->
<!-- ASSUMPTION: Cocotb tests are discoverable by pytest in the validation directory tree. -->

# Co-simulation Runner Steps

## Prerequisites

Install or make available the following tools:

- Verilator
- Python 3
- cocotb
- pytest
- A C/C++ toolchain required by Verilator builds
- Any firmware build tools required by this project, if firmware artifacts are used

Recommended Python packages:

- cocotb
- pytest
- pytest-junitxml (typically included via pytest; XML output is optional)
- any project-specific Python dependencies

## Inputs

Environment overrides expected by the runner script:

- `RTL_TOP=${RTL_TOP:-<RTL_TOP>}`
- `RTL_DIR=${RTL_DIR:-<RTL_DIR>}`
- `FILELIST=${FILELIST:-<FILELIST>}`

Optional environment overrides:

- `FW_BUILD_DIR=${FW_BUILD_DIR:-firmware/validate/fw_build}`
- `COSIM_OUT_DIR=${COSIM_OUT_DIR:-firmware/validate/cosim_out}`
- `PYTEST_ARGS=${PYTEST_ARGS:-}`

## Build and Run Flow

If `firmware/validate/verilator_build.md` exists, follow that document for the RTL simulation build. Otherwise, use the generic sequence below.

### 1) Build the RTL simulator

Use the Verilator build command described in `firmware/validate/verilator_build.md` when available.

If no project-specific build command is provided, the generic expectation is:

1. Generate the Verilator model from the RTL top, RTL directory, and filelist.
2. Build the simulator shared object or executable used by cocotb/pytest.
3. Place build artifacts under `firmware/validate/`.

Example generic command pattern:

- `verilator <RTL build options> --top-module "${RTL_TOP}" --Mdir "${COSIM_OUT_DIR}/verilator_build" -f "${FILELIST}"`

The exact flags must match the project’s Verilator build flow.

### 2) Build firmware, if applicable

If the DUT requires firmware artifacts, build them before running cocotb.

Example generic command pattern:

- `make -C <firmware_dir> आउट=...`
- or the project-specific firmware build command

Place any firmware outputs under `firmware/validate/fw_build/` or another directory referenced by the testbench.

If firmware is not required, skip this step.

### 3) Run cocotb via pytest

Execute cocotb tests using pytest from the validation directory.

Generic command pattern:

- `pytest -q firmware/validate ${PYTEST_ARGS} --junitxml=firmware/validate/cosim_out/junit.xml`

If the environment uses a different cocotb entrypoint, ensure it is still invoked through `pytest -q ...`.

## Expected Outputs

The runner should generate outputs under `firmware/validate/`, typically including:

- Build logs
- Verilator build artifacts
- cocotb simulation logs
- pytest test summary
- Optional JUnit XML report, such as:
  - `firmware/validate/cosim_out/junit.xml`
- Optional coverage artifacts if enabled by the build flow
- Optional waveform files if enabled by the testbench

## Notes

- The exact build and runtime commands must be consistent with the project’s Verilator and cocotb integration.
- The runner script intentionally avoids hardcoding RTL file paths and expects environment overrides.
- If `firmware/validate/verilator_build.md` is present, it should be treated as the source of truth for RTL build invocation.
