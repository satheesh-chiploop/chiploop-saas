# ChipLoop V&V: Cocotb + Verilator

Generated:
- `test_pwm_controller.py`     : cocotb tests
- `Makefile`          : cocotb/verilator make entry
- `rtl_sources.mk`    : explicit RTL file list
- `testcases.json`    : testcase manifest
- `tb_contract.json`  : resolved contract used for testbench generation
- `verification_plan.md`, `monitor_checker_plan.md`, `coverage_point_plan.md` : generated or uploaded review plans

Run (from this folder):
```bash
make
RANDOM_SEED=123 make
NUM_ITERS=200 RANDOM_SEED=7 make TESTCASE=constrained_random_sanity
python run_regression.py --tests smoke_test constrained_random_sanity --seeds 1 2 3 4
```
