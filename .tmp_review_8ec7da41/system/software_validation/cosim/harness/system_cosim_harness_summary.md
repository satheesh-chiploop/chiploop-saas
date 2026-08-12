# System Software CoSim Harness Summary

- Generated at: `2026-08-12T19:01:03.929817+00:00`
- L1 ready: `None`
- Harness status: `ready`
- Scenario count: `9`

## Blocked dependencies
- none

## Resolved commands
- `control_service_boot_smoke` → `make -C /root/chiploop-backend/artifacts/3c6dfa47-ba1d-4be5-857c-c60b38fc0ff6/8ec7da41-59b5-4ffa-8177-d3c4db4628f1/f3c51375-b803-460e-b45e-990e3112bfb4/system/system/restored_rtl_sim/48808218-e19e-4861-9646-b7dc0a105149/vv/tb`
- `control_service_boot_smoke` → `cargo run -p ss_app_control_service -- --scenario control_service_boot_smoke`
- `control_service_register_rw_basic` → `cargo run -p ss_app_control_service -- --scenario control_service_register_rw_basic`
- `diagnostics_boot_smoke` → `cargo run -p ss_app_diagnostics -- --scenario diagnostics_boot_smoke`
- `diagnostics_register_rw_basic` → `cargo run -p ss_app_diagnostics -- --scenario diagnostics_register_rw_basic`
- `demo_cli_boot_smoke` → `cargo run -p ss_app_demo_cli -- --scenario demo_cli_boot_smoke`
- `demo_cli_register_rw_basic` → `cargo run -p ss_app_demo_cli -- --scenario demo_cli_register_rw_basic`
