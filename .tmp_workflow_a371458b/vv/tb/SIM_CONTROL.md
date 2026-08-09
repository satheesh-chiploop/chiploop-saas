# Simulation Control

Generated:
- `run_regression.py` : orchestrates multi-seed runs via `make TESTCASE=...`

Seed management:
- override with `RANDOM_SEED=<int>`

Usage:
```bash
python run_regression.py --tests smoke_test constrained_random_sanity --seeds 1 2 3 4 5
```
