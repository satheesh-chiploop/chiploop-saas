# UPF Static Check

- Status: `fail`
- UPF file: `missing`
- Power domains: `0`
- Supply ports/nets: `0/0`
- Isolation rules: `0`
- Retention rules: `0`
- Level shifter rules: `0`
- PST/power states: `missing`
- OpenROAD read_upf: `not_run`
- Private adapter: `not_configured`

This is an open-source-compatible structural UPF check. It is not a replacement for commercial power-aware simulation or signoff.

## Checks
- `upf_present`: `fail` No UPF artifact found.
- `power_domains`: `fail` No create_power_domain command found.
- `supplies`: `fail` Missing supply ports or supply nets.
- `domain_supply_mapping`: `pass`
- `domain_elements_resolve`: `not_run` No RTL files available for element resolution.
- `unsupported_commands`: `pass`
- `isolation_intent`: `pass`
- `retention_intent`: `pass`
- `level_shifter_intent`: `pass`
- `power_state_table`: `warn` No PST/power states found.
