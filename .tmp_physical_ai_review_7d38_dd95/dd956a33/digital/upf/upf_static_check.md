# UPF Static Check

- Status: `warn`
- UPF file: `power_intent.upf`
- Power domains: `1`
- Supply ports/nets: `2/2`
- Isolation rules: `0`
- Retention rules: `0`
- Level shifter rules: `0`
- PST/power states: `missing`
- OpenROAD read_upf: `tool_unavailable`
- Private adapter: `not_configured`

This is an open-source-compatible structural UPF check. It is not a replacement for commercial power-aware simulation or signoff.

## Checks
- `upf_present`: `pass` power_intent.upf
- `power_domains`: `pass`
- `supplies`: `pass`
- `domain_supply_mapping`: `pass`
- `domain_elements_resolve`: `pass`
- `unsupported_commands`: `pass`
- `isolation_intent`: `pass`
- `retention_intent`: `pass`
- `level_shifter_intent`: `pass`
- `power_state_table`: `warn` No PST/power states found.
