# firmware/integration_contract.md

## Contract overview
- This firmware is a Rust PWM fan-control layer over the verified `pwm_controller` RTL imported from Arch2RTL.
- Firmware owns the policy decision and register programming for `enable`, `period`, and `duty-cycle`.
- The observable hardware output is `pwm_out`; validation must confirm `pwm_out` tracks the programmed duty cycle at the configured period.
- Temperature-to-duty policy is fixed:
  - `< 30 C` → `0%`
  - `30 C to 49 C` → `25%`
  - `50 C to 69 C` → `55%`
  - `>= 70 C` → `90%`
- Rust register access must be the only software path for programming the PWM RTL in this scope.
- Co-simulation is enabled and must be used to validate register writes against RTL behavior.
- Coverage is enabled and must be collected on register access sequences and duty-cycle boundary conditions.
- The handoff package must include the register layer, driver, test collateral, cosim collateral, and a validation report.

## Contract version + compatibility policy
- **Contract version:** `1.0.0`
- **Compatibility policy:**
  - **Patch updates** (`1.0.x`) may clarify wording, add non-functional validation detail, or extend test collateral without changing register semantics.
  - **Minor updates** (`1.x.0`) may add new software APIs only if they remain backward compatible with the existing PWM register contract.
  - **Major updates** (`x.0.0`) may change register semantics, policy mapping, or ownership boundaries and require re-validation of the RTL/FW interface.
- **Source of truth:** the imported Arch2RTL-generated PWM RTL and its completed register map.
- **Version binding:** firmware must embed a compile-time contract version string and fail build if the imported register map version does not match the expected major version.

## Interfaces

### Register interface
| Name | Direction | Description | Firmware responsibility |
|---|---:|---|---|
| `enable` | W | Enables or disables PWM output generation | Set according to thermal policy; `0` for fan off |
| `period` | W | PWM period setting | Program from RTL-defined timing contract |
| `duty_cycle` | W | Duty-cycle setting | Set to one of the policy values mapped from temperature |
| `pwm_out` | R/O observable | Fan-control output from RTL | Read in validation only; not driven by firmware |

### Software API
| API | Inputs | Output / effect | Notes |
|---|---|---|---|
| `PwmFanDriver::init()` | None | Initializes register block and default safe state | Must leave fan in a deterministic safe state |
| `PwmFanDriver::apply_temperature(temp_c)` | `u32` temperature in Celsius | Updates `enable`, `period`, and `duty_cycle` | Implements policy mapping exactly |
| `PwmFanDriver::set_mode(mode)` | Operational mode enum | Selects control behavior | Supported modes must be documented in code and tests |
| `PwmFanDriver::read_back()` | None | Reads current programmed state | Used for validation and diagnostics |

### Error codes
| Code | Name | Meaning | Required handling |
|---|---|---|---|
| `0x00` | `OK` | Operation completed successfully | No action |
| `0x01` | `ERR_RANGE` | Input outside supported thermal range representation | Clamp or reject per API contract |
| `0x02` | `ERR_HW_TIMEOUT` | RTL/register access did not complete as expected | Report to host; enter safe fan state |
| `0x03` | `ERR_VERSION_MISMATCH` | Firmware/register map version mismatch | Fail init and halt PWM control |

### Logging schema
| Field | Type | Description |
|---|---|---|
| `ts` | u64 | Firmware timestamp or monotonic tick |
| `level` | string | `INFO`, `WARN`, or `ERROR` |
| `module` | string | `pwm_fan` |
| `event` | string | Stable event name |
| `temp_c` | u32 optional | Input temperature for policy decisions |
| `duty_pct` | u8 optional | Selected duty percentage |
| `enable` | bool optional | Applied enable state |
| `status` | string optional | Result or error code name |

### Power modes
| Mode | Firmware behavior | PWM behavior |
|---|---|---|
| Active | Apply policy periodically or on input update | Normal register-controlled operation |
| Low-power | Preserve current safe output state unless explicitly updated | No policy-driven change unless firmware is awake |
| Reset/boot | Program safe default state before release | `enable=0` until initialization completes |

## Ownership boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| Thermal policy mapping | Owns and implements | Supplies temperature input | Verifies exact boundary behavior |
| Register programming | Owns | May request updates through API | Checks writes match RTL map |
| RTL behavior (`pwm_controller`) | Consumes as verified hardware | No ownership | Validates against imported RTL |
| `pwm_out` observation | Not driven | Not owned | Monitors waveform and duty accuracy |
| Error reporting | Emits contract-defined codes/logs | Consumes logs and errors | Confirms schema and code coverage |

## Assumptions
- The imported PWM RTL register map is finalized and available to Rust as generated bindings.
- `period` semantics, clocking, and reset behavior are fully defined by the RTL contract.
- The duty-cycle values `0%`, `25%`, `55%`, and `90%` are representable in the RTL’s duty register encoding.
- Temperature input is supplied by system software or a sensor service; firmware does not implement sensor acquisition in this contract.
- Co-simulation has a cycle-accurate RTL model and a Rust test harness capable of issuing register writes and sampling `pwm_out`.
- Coverage collection is available for register access paths and boundary-value policy transitions.
- Firmware must fail safe by disabling PWM output if initialization or version checks fail.

## Validation hooks
- **Build-time register compatibility check:** confirm the generated Rust register layer matches the imported RTL register map version and field layout.
- **Unit tests for policy mapping:** verify exact thresholds at `29, 30, 49, 50, 69, 70 C`.
- **Register write/readback tests:** confirm `enable`, `period`, and `duty_cycle` values are written and read back correctly.
- **Co-simulation duty validation:** drive each policy state and check `pwm_out` duty matches expected percentages within RTL timing resolution.
- **Safe-state validation:** on init failure, version mismatch, or invalid input handling, confirm `enable=0` and `pwm_out` remains inactive.
- **Coverage checks:** require coverage on:
  - all temperature boundary transitions,
  - enable/disable paths,
  - all register write sequences,
  - error paths and safe-state fallback.
- **Software-facing handoff review:** verify the API, error codes, logging schema, and ownership boundaries are documented and consumed by system software.