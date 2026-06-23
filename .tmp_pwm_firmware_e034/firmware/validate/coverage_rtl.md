<!-- ASSUMPTION: RTL coverage capability depends on simulator version and compile-time flags. -->
<!-- ASSUMPTION: Confirm supported flags with `verilator --help` before enabling coverage in CI. -->

# RTL Coverage Collection

- Verilator available in environment: `True`
- Example command template:
```bash
verilator <VERILATOR_COVERAGE_FLAGS> --cc --build --trace -f firmware/validate/verilator_rtl_filelist.f
./obj_dir/V<top_module>
```
- Common coverage flag examples to verify against your version:
  - `--coverage`
  - `--coverage-line`
  - `--coverage-toggle`
- Expected report location: simulator output directory, version-dependent.
- If unsupported, report RTL coverage as unavailable rather than inventing percentages.
