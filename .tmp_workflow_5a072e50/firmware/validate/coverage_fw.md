<!-- ASSUMPTION: Firmware coverage collection depends on the actual firmware language/toolchain used in this workflow. -->
<!-- ASSUMPTION: Confirm compiler and target support before enabling instrumentation in CI. -->

# Firmware Coverage Collection

## Method A: Rust coverage (cargo-llvm-cov)
- Available in environment: `False`
- Target triple: `x86_64-unknown-linux-gnu`
- Binary name: `firmware_app`
- Example command template:
```bash
cargo llvm-cov --no-report --release --target <TARGET_TRIPLE>
cargo llvm-cov report --html
```
- Expected report location: `target/llvm-cov/html/index.html`

## Method B: GCC/gcov style coverage
- Available in environment: `True`
- Example command template:
```bash
<CC> --coverage -o <BIN_NAME> <SOURCES>
./<BIN_NAME>
gcov <SOURCE_FILE>
```
- Expected report location: `*.gcov` beside instrumented sources or build directory.

## Method C: Not supported in v1
- Use this when the firmware toolchain is neither Rust nor GCC-compatible, or when target execution cannot emit host-readable coverage data.
- Enable later by adding toolchain-specific instrumentation and export steps.

## Recommendation
- Pick the method that matches the actual firmware compiler in this workflow.
- Do not fabricate coverage numbers if instrumentation was not enabled.
