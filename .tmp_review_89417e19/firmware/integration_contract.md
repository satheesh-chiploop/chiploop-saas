# Firmware Integration Contract

## Contract Overview

- Defines the firmware-to-system/host integration contract for the full Embedded_Run chain.
- Covers API behavior, power/state transitions, logging, error reporting, and versioning.
- Establishes stable ownership boundaries between firmware, system/host software, and validation.
- Requires deterministic boot-to-ready signaling and explicit failure handling.
- Requires register validation when `validate_registers` is enabled.
- Supports co-simulation when `enable_cosim` is enabled, with no change to external API semantics.
- All contract-visible behaviors must be backward compatible within a major version.
- Any contract break requires a major version bump and corresponding host-side update.

## Contract Version + Compatibility Policy

**Contract Version:** `1.0.0`

**Compatibility policy:**
- **Patch updates** (`1.0.x`): bug fixes only; no interface or behavior changes.
- **Minor updates** (`1.x.0`): additive changes only; existing APIs, error codes, and log schema remain valid.
- **Major updates** (`x.0.0`): breaking changes allowed; requires coordinated firmware and host update.
- Firmware must expose its contract version at runtime.
- Host/system software must refuse to run if the major version is incompatible.

## Interfaces

### 1) Runtime Control Interface

| Interface | Direction | Description | Behavior | Failure Mode |
|---|---|---|---|---|
| `fw_init()` | Host/System → FW | Initialize firmware-managed runtime services | Must be idempotent before `fw_ready()`; subsequent calls after ready are rejected | `ERR_STATE`, `ERR_BUSY` |
| `fw_start()` | Host/System → FW | Transition firmware into operational state | Must complete only after internal initialization succeeds | `ERR_STATE`, `ERR_HW` |
| `fw_stop()` | Host/System → FW | Transition firmware into stopped/safe state | Must quiesce firmware-owned activities and preserve stop reason | `ERR_STATE` |
| `fw_get_status()` | Host/System → FW | Query current firmware state | Returns current state and last error atomically | `ERR_NONE` or status-only return |
| `fw_get_version()` | Host/System → FW | Retrieve contract and firmware version | Must return semantic version and build metadata | `ERR_NONE` |

### 2) Boot-to-Ready Signaling

| Interface | Direction | Description | Behavior | Failure Mode |
|---|---|---|---|---|
| `BootLog` | FW → Host/System | Structured boot progress reporting | Must be emitted during boot and include major milestones | Logging failure must not block boot |
| `ReadySignal` | FW → Host/System | Indicates firmware is ready for normal operation | Must be asserted only after initialization checks pass | If not asserted, host treats boot as failed |
| `BootFailurePolicy` | FW → Host/System | Defines boot failure handling | On fatal boot error, firmware must report failure and remain non-operational | Must not silently continue |

### 3) Error Reporting Interface

| Error Code | Meaning | Recoverability | Typical Source |
|---|---|---|---|
| `ERR_NONE` | No error | N/A | Success path |
| `ERR_STATE` | Invalid state transition | Recoverable if caller corrects sequence | API misuse |
| `ERR_BUSY` | Firmware is busy or not ready | Recoverable | Concurrent operation |
| `ERR_TIMEOUT` | Operation exceeded allowed time | Possibly recoverable | Initialization or sync |
| `ERR_HW` | Hardware/low-level failure | Depends on subsystem state | Init, platform bring-up |
| `ERR_CONFIG` | Invalid configuration or incompatible version | Recoverable after fix | Host configuration |
| `ERR_INTERNAL` | Unexpected internal failure | Usually non-recoverable for current session | Assertion/fault path |

### 4) Logging Schema

| Field | Type | Required | Description |
|---|---|---:|---|
| `ts_us` | integer | Yes | Monotonic timestamp in microseconds |
| `level` | string | Yes | One of `DEBUG`, `INFO`, `WARN`, `ERROR`, `FATAL` |
| `module` | string | Yes | Firmware module identifier |
| `event` | string | Yes | Stable event name |
| `code` | string | Yes | Contract error code or event code |
| `message` | string | Yes | Human-readable summary |
| `context` | object | No | Key/value details relevant to the event |

**Logging requirements:**
- Boot logs must include at least: reset cause, version, init start, init complete or failure, ready asserted.
- Error logs must include a contract error code.
- Log format must be stable across minor versions.

### 5) Versioning Interface

| Item | Requirement |
|---|---|
| Semantic version | `major.minor.patch` |
| Runtime exposure | Firmware must provide version via API or boot log |
| Compatibility check | Host/system software must validate major version |
| Build metadata | Optional, but if present must not affect compatibility parsing |

### 6) Register Validation Contract

| Item | Requirement |
|---|---|
| `validate_registers = true` | Firmware must verify all contract-visible registers before entering ready state |
| Validation timing | Must occur before `ReadySignal` |
| Failure behavior | Any invalid register value must prevent ready state and raise `ERR_CONFIG` or `ERR_HW` |
| Reporting | Validation failures must be logged with register name/address and observed value |
| Host expectation | Host/system must not assume silent correction |

### 7) Co-simulation Contract

| Item | Requirement |
|---|---|
| `enable_cosim = true` | Firmware must support co-sim execution without changing observable API semantics |
| Timing | Co-sim may alter timing but not ordering guarantees for contract-visible events |
| Logging | Co-sim-specific markers may be added but must not replace required boot/status logs |
| Validation | Co-sim runs must produce the same ready/failure outcomes for the same inputs |

## Ownership Boundaries

| Area | FW Ownership | System/Host Ownership | Validation Ownership |
|---|---|---|---|
| Boot sequencing | Implements boot, init, ready/failure signaling | Observes and gates execution on ready/failure | Verifies sequence and timing |
| Runtime APIs | Implements API behavior and error codes | Calls APIs in supported order | Checks return codes and state transitions |
| Logging | Emits structured logs and codes | Collects and persists logs | Validates schema and required events |
| Versioning | Publishes contract/runtime version | Checks compatibility before use | Confirms version policy compliance |
| Register validation | Validates firmware-owned contract registers | Supplies expected configuration values | Injects invalid values and checks rejection |
| Failure handling | Detects and reports fatal/non-fatal failures | Stops relying on firmware after fatal failure | Verifies failure paths and recovery boundaries |

## Assumptions

- The firmware exposes a single stable contract for the Embedded_Run full-chain integration.
- Host/system software can read firmware logs and status before issuing operational commands.
- There is a deterministic ready/failure point during boot.
- Register validation applies only to contract-visible registers, not internal implementation details.
- `enable_cosim` affects test execution environment only, not the public contract.
- No undocumented side effects are permitted on successful API calls.
- Major-version mismatch is treated as an incompatible contract.

## Validation Hooks

Use the following checks to prove contract compliance:

1. **Version check**
   - Read runtime version.
   - Confirm major version matches host expectation.
   - Reject incompatible major versions.

2. **Boot sequence check**
   - Capture boot logs.
   - Verify required milestones appear in order.
   - Confirm exactly one terminal outcome: ready or failure.

3. **Ready gating check**
   - Attempt operational calls before ready.
   - Confirm they fail with `ERR_STATE` or `ERR_BUSY` as appropriate.
   - Confirm normal calls succeed only after ready.

4. **Register validation check**
   - With `validate_registers = true`, inject valid and invalid register values.
   - Confirm valid values allow ready.
   - Confirm invalid values prevent ready and generate `ERR_CONFIG` or `ERR_HW`.

5. **Error code check**
   - Force each defined failure class where possible.
   - Verify returned codes and logged codes match the contract.

6. **Logging schema check**
   - Parse logs against the required field set.
   - Confirm timestamps, levels, module, event, code, and message are present.
   - Confirm boot and error logs include the required events.

7. **Co-sim equivalence check**
   - Run the same test vector with `enable_cosim = true` and non-cosim execution.
   - Verify identical contract-visible outcomes, including ready/failure and error codes.

8. **Stop-state check**
   - Issue `fw_stop()`.
   - Confirm firmware transitions to a safe stopped state.
   - Confirm operational APIs reject further use until reinitialized.