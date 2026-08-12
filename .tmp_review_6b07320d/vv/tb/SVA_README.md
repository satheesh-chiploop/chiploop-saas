# System SVA Usage

Generated:
- `temp_monitor_soc_sim_assertions.sv`        : assertion module derived from system integration/top-level contract
- `temp_monitor_soc_sim_assertions_bind.sv`   : bind file for DUT integration
- `sva_spec.json`           : resolved system assertion contract
- `sva_generation_report.json`

Primary sources used:
- system integration intent
- system top simulation module
- digital register map (when present, for metadata/reporting only)

The bind file uses only resolved top-level signals and is intended to be compiled with simulation sources.
