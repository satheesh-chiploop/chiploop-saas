# Functional Coverage (Cocotb)

Generated:
- `coverage_model.py`       : lightweight functional coverage sampler
- `coverage_spec.json`      : resolved coverage points derived from spec
- `coverage_generation_report.json` : concise agent output report

Usage (in cocotb tests):
- cov = CoverageModel()
- cov.start(dut)
- cov.sample() at transaction boundaries or checkpoints
- cov.stop()
- cov.write_reports() at end of sim

Reports emitted by CoverageModel:
- `reports/functional_coverage_summary.json`
- `reports/COVERAGE.md`
