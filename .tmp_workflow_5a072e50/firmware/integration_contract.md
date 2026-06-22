# Firmware Integration Contract

## Contract overview
- This contract defines the firmware-facing integration surface generated from the imported Arch2RTL RTL interface and register map.
- It covers API behavior, initialization, error reporting, logging, versioning, power-state handling, and ownership boundaries for the full Embedded_Run / full-chain flow.
- Firmware shall interact only through the generated register layer and the exported driver scaffold; no direct register assumptions outside the published map.
- System/Host software owns orchestration above the firmware API, including policy decisions, user-visible sequencing, and recovery escalation.
- Firmware owns deterministic device bring-up, register programming, status polling, fault detection, and structured error reporting for the imported RTL block.
- Validation owns contract compliance checking against RTL behavior, register map consistency, and co-simulation results where enabled.
- Co-simulation and coverage hooks are included because the requested toggles enable both.
- This document is intended as the software-facing handoff for the actual imported design, not a generic template.

## Contract version + compatibility policy
| Item | Value |
|---|---|
| Contract version | 1.0.0 |
| Source of truth | Generated RTL interface + generated register map from Arch2RTL workflow |
| Compatibility policy | Backward-compatible changes must preserve existing register offsets, field semantics, and API signatures |
| Breaking changes | Require major version increment and explicit validation re-signoff |
| Version reporting | Firmware shall expose the contract version through a read-only version query and log it during init |
| Register map drift policy | Any RTL/register-map drift invalidates the contract until regenerated and revalidated |

## Interfaces

### Firmware API interface
| API | Inputs | Outputs | Expected behavior | Error handling |
|---|---|---|---|---|
| `fw_init()` | None | Status code | Initializes the device, validates register accessibility, programs required defaults, and transitions to ready state when hardware is responsive | Returns a contract-defined error if reset/state/clock checks fail |
| `fw_get_version()` | None | Contract version string/tuple | Returns the firmware contract version matching this document | Must not mutate state |
| `fw_read_status()` | None | Status snapshot | Reads live device status from the generated register layer | Must return stable snapshot semantics for the read path |
| `fw_clear_faults(mask)` | Fault mask | Status code | Clears acknowledged sticky faults according to the register map semantics | Rejects invalid masks or unsupported fault bits |
| `fw_set_mode(mode)` | Enumerated mode | Status code | Programs the device mode only if the mode is supported by the imported RTL | Rejects unsupported or illegal transitions |
| `fw_get_log_entry(index)` | Log index | Structured log record | Returns firmware-maintained structured log data | Returns out-of-range error for invalid indices |
| `fw_shutdown()` | None | Status code | Places the device into the defined low-activity or safe-off state when supported | Must leave hardware in a documented safe state |

### Register layer interface
| Register-layer element | Responsibility | Behavior |
|---|---|---|
| Base address binding | Maps the imported RTL register block into firmware address space | Must match generated map exactly |
| Field accessors | Encodes/decodes bitfields from the RTL map | Must preserve reserved bits unless specified otherwise |
| Read/modify/write helpers | Applies safe masked updates | Must not clobber unrelated fields |
| Status polling helpers | Waits on ready/busy/fault conditions | Must use bounded timeout behavior |
| Reset helpers | Issues software-visible reset sequencing where supported | Must follow RTL-defined reset ordering |

### Logging and error model
| Item | Contract |
|---|---|
| Log format | Structured records with timestamp, severity, subsystem, opcode/context, and result code |
| Severity levels | DEBUG, INFO, WARN, ERROR, FATAL |
| Error codes | Must be enumerated and stable; include at minimum `OK`, `TIMEOUT`, `INVALID_PARAM`, `HW_FAULT`, `UNSUPPORTED`, `BUS_ERROR`, `STATE_ERROR` |
| Log ownership | Firmware owns device-facing logs; System/Host may consume but not redefine schema |
| Fatal behavior | Fatal hardware or integrity failures must be reported and block further normal operation until reset/recovery per policy |

### Power mode / state interface
| State | Firmware behavior | Host expectation |
|---|---|---|
| Reset | Firmware performs no unsafe writes until register accessibility is confirmed | Host may hold orchestration until ready signal |
| Ready | Firmware may service normal API calls | Host may issue runtime operations |
| Low-power / quiescent | Firmware shall preserve required state and avoid unsupported accesses | Host must not assume full functionality unless re-enabled |
| Fault | Firmware shall report fault condition and restrict operations to status/query/clear where safe | Host must initiate recovery per system policy |

## Ownership boundaries
| Area | FW owns | System/Host owns | Validation owns |
|---|---|---|---|
| Register programming | Yes | No | Checks correctness |
| Mode sequencing | Yes, within device limits | Yes, policy/ordering above FW | Verifies transitions |
| Error interpretation | Yes, device-local codes and status | Consumes and escalates | Confirms mapping |
| Recovery policy | Limited to device-safe recovery actions | Full system recovery decisions | Tests recovery paths |
| Logging schema | Yes | Consume only | Validates format/content |
| Versioning | Yes, contract version exposure | Tracks compatibility | Confirms advertised version |
| RTL contract compliance | No | No | Yes |

## Assumptions
- The imported RTL package provides a generated, authoritative register map and interface description.
- The hardware block exposes a stable software-visible base address and reset behavior in the generated collateral.
- The firmware target has a standard memory-mapped I/O path suitable for register access.
- No undocumented sideband control path is assumed beyond the generated RTL interface.
- Any capability not present in the generated register map is considered unsupported by this contract.
- Coverage and co-simulation infrastructure are available in the validation environment because the requested toggles are enabled.

## Validation hooks
| Hook | Method | Pass criteria |
|---|---|---|
| Register map conformance | Compare firmware accessor definitions against generated RTL register map | Exact offset/field match, no reserved-bit violations |
| Init sequence compliance | Run `fw_init()` against RTL model and hardware | Reaches ready state within bounded timeout and logs version/status |
| Error-path verification | Inject invalid parameters and hardware fault conditions | Correct error codes returned, no unsafe state changes |
| Read/write correctness | Exercise all supported registers and fields via generated accessors | RTL-observed values match expected encode/decode behavior |
| State transition checks | Exercise reset/ready/fault/low-power transitions | Only allowed transitions occur; illegal transitions rejected |
| Log schema validation | Capture firmware logs during bring-up and fault events | Records match the required structured schema |
| Co-simulation check | Run firmware against RTL model in co-sim mode | Control/status behavior matches expected contract |
| Coverage review | Measure exercised API paths and register fields | Contract-relevant paths reach agreed coverage thresholds |
| Version check | Read contract version from firmware and compare to document | Exact match |
| Handoff review | Inspect exported headers, docs, and error definitions | All public software-facing artifacts align with this contract |

## Software-facing handoff package
| Artifact | Purpose | Owner |
|---|---|---|
| Generated register layer | Typed access to imported RTL registers | Firmware |
| Driver scaffold | Minimal device driver entry points and lifecycle hooks | Firmware |
| API header | Public software-facing declarations | Firmware |
| Error code header | Stable device-local error enumeration | Firmware |
| Log schema document | Structured logging format and field definitions | Firmware |
| Validation report | Results of RTL/firmware contract checks | Validation |
| Co-simulation collateral | Test harness inputs and run instructions | Validation |
| Coverage summary | Exercised APIs/registers and gaps | Validation |

## Notes on contract enforcement
- Firmware must treat the generated register map as the only authoritative hardware interface.
- Any mismatch between RTL, register map, and exported headers is a contract violation.
- System/Host software may rely on the published API and error codes, but not on undocumented register behavior.
- Validation signoff is required before this collateral can be considered release-ready.