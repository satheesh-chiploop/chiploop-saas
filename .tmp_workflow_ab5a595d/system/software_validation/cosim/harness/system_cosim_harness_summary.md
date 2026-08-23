# System Software CoSim Harness Summary

- Generated at: `2026-08-23T05:43:26.252782+00:00`
- L1 ready: `True`
- Harness status: `blocked`
- Scenario count: `9`

## Blocked dependencies
- `rtl_cosim_command_missing`

## Resolved commands
- `control_service_boot_smoke` → `cargo run -p ss_app_control_service -- --scenario control_service_boot_smoke`
- `control_service_register_rw_basic` → `cargo run -p ss_app_control_service -- --scenario control_service_register_rw_basic`
- `diagnostics_boot_smoke` → `cargo run -p ss_app_diagnostics -- --scenario diagnostics_boot_smoke`
- `diagnostics_register_rw_basic` → `cargo run -p ss_app_diagnostics -- --scenario diagnostics_register_rw_basic`
- `demo_cli_boot_smoke` → `cargo run -p ss_app_demo_cli -- --scenario demo_cli_boot_smoke`
- `demo_cli_register_rw_basic` → `cargo run -p ss_app_demo_cli -- --scenario demo_cli_register_rw_basic`
