# Firmware Integration Contract

## 1) Contract overview
- Defines the firmware-facing integration contract for the full Embedded_Run chain, including API behavior, logging, error reporting, versioning, and ownership boundaries.
- Establishes what firmware guarantees to System/Host software and what System/Host must provide to firmware.
- Specifies stable interfaces, expected call/response behavior, and required status/error semantics.
- Defines power-mode and reset behavior at the contract level, including how readiness and failure are reported.
- Uses versioned compatibility rules to preserve interoperability across firmware and host releases.
- Requires structured logging with fixed schema elements so validation and host-side parsers remain stable.
- Separates responsibilities across Firmware, System/Host, and Validation to prevent overlap and ambiguous ownership.
- Provides validation hooks to verify contract compliance in bring-up, regression, and release testing.

## 2) Contract version + compatibility policy

**Contract version:** `1.0.0`

**Compatibility policy:**
- **Backward-compatible changes** are allowed in patch and minor updates if they do not change existing field meanings, required behaviors, or error code semantics.
- **New optional fields** may be added to logs or informational responses if old consumers can ignore them.
- **Breaking changes** require a major version bump and explicit host-side coordination.
- Firmware shall report its contract version at runtime in a machine-readable form.
- System/Host shall reject or downgrade features when the advertised contract version is outside the supported range.
- Validation shall treat any mismatch in required behavior, status codes, or field definitions as a contract failure.

## 3) Interfaces

### 3.1 Runtime control interface

| Interface | Direction | Type | Required Behavior | Error/Status Semantics | Ownership |
|---|---|---|---|---|---|
| `GetContractVersion()` | Host -> FW | Query | Return contract version string/tuple exactly matching the compiled firmware contract. | Returns `OK` on success; `UNSUPPORTED` if unavailable. | FW provides; Host consumes |
| `GetFirmwareState()` | Host -> FW | Query | Return current state: `RESET`, `INIT`, `READY`, `BUSY`, `ERROR`, or implementation-specific state mapped to these canonical states. | Returns `OK` with state payload; `INVALID_STATE` if state cannot be represented. | FW provides; Host consumes |
| `EnterPowerMode(mode)` | Host -> FW | Command | Request transition to supported power mode. Firmware must validate safety and return deterministically. | `OK`, `INVALID_PARAM`, `BUSY`, `UNSUPPORTED`, `FAILED`. | FW executes policy; Host requests |
| `GetPowerMode()` | Host -> FW | Query | Return current active power mode. | `OK` with mode payload. | FW provides; Host consumes |
| `ResetRequest(type)` | Host -> FW | Command | Request a controlled reset type if supported. Firmware must either schedule it or reject it. | `OK`, `UNSUPPORTED`, `DENIED`, `FAILED`. | FW executes reset policy; Host requests |
| `GetLastError()` | Host -> FW | Query | Return last sticky error code and context identifier if supported. | `OK`; returns zero/no-error when clear. | FW provides; Host consumes |
| `ClearError()` | Host -> FW | Command | Clear recoverable error state only if allowed by firmware policy. | `OK`, `DENIED`, `FAILED`. | FW policy-owned; Host may request |

### 3.2 Status and error model

| Code | Meaning | Recoverable | Notes |
|---|---|---:|---|
| `OK` | Operation succeeded | N/A | Canonical success code |
| `INVALID_PARAM` | Input parameter invalid or out of range | Yes | No state change guaranteed |
| `UNSUPPORTED` | Feature/interface not supported by this firmware build | Yes | Stable across versions |
| `BUSY` | Firmware cannot accept request now | Yes | Retry permitted if documented by host policy |
| `DENIED` | Request rejected by firmware policy/state | Maybe | Typically state or privilege gated |
| `FAILED` | Operation failed unexpectedly | Maybe | Requires log context |
| `INVALID_STATE` | Request/state mismatch | Yes | Host must re-query state |
| `TIMEOUT` | Operation did not complete in expected time | Yes | Host may retry per policy |

### 3.3 Logging schema

| Field | Type | Required | Description |
|---|---|---:|---|
| `ts` | uint64 / monotonic timestamp | Yes | Firmware-local timestamp or tick value |
| `level` | enum | Yes | `DEBUG`, `INFO`, `WARN`, `ERROR`, `FATAL` |
| `module` | string or numeric ID | Yes | Source component identifier |
| `event_id` | uint32 | Yes | Stable event identifier |
| `status` | code | Yes | Result or associated error code |
| `message` | string | Yes | Human-readable summary |
| `context` | key-value payload | Optional | Structured diagnostic data |
| `contract_version` | string/tuple | Recommended | Version active at event time |

**Logging rules:**
- Event IDs must remain stable within a major contract version.
- Error logs must include the associated status code and enough context to diagnose without firmware source access.
- Host parsers must not rely on free-form message text for programmatic decisions.

### 3.4 Versioning and feature negotiation

| Item | Rule |
|---|---|
| Contract identification | Firmware shall expose contract version at runtime |
| Major version | Indicates breaking compatibility boundary |
| Minor version | Indicates additive, backward-compatible changes |
| Patch version | Indicates non-functional fixes and clarifications |
| Feature gating | Host shall check advertised version before enabling version-dependent behavior |
| Fallback behavior | If unsupported, host shall use the safest compatible path or disable the feature |

### 3.5 Power mode behavior

| Power Mode | Firmware Behavior | Host Expectation |
|---|---|---|
| `ACTIVE` | Full operational readiness | Normal operation allowed |
| `LOW_POWER` | Reduced activity; maintain required control plane only | Reduced-rate access; some commands may return `BUSY` |
| `SLEEP` | Minimum activity compatible with wake behavior | Host must not expect normal service |
| `OFF` | No operational service except documented wake/reset path | Host must treat as unavailable |

**Power-mode rules:**
- Firmware shall reject transitions that violate safety, data integrity, or state requirements.
- Host shall not assume instantaneous transition; it must observe returned status and re-query state if needed.
- If a transition fails, firmware shall preserve the pre-existing valid state unless a fatal error is reported.

### 3.6 Reset and readiness behavior

| Interface | Required Behavior | Host Expectation |
|---|---|---|
| Reset cause reporting | Firmware shall preserve and expose the last reset cause until cleared by the defined boot path | Host shall read and record reset cause during initialization |
| Ready signaling | Firmware shall assert readiness only after initialization is complete and required services are available | Host shall not issue normal runtime commands before ready is asserted |
| Boot failure behavior | Firmware shall enter a deterministic failure state or safe reset loop per policy | Host shall detect failure and avoid unsafe command retries |

## 4) Ownership boundaries

| Area | Firmware owns | System/Host owns | Validation owns |
|---|---|---|---|
| Contract implementation | Command handling, state transitions, error returns, logging emission | Consumer logic, retries, compatibility checks | Contract compliance tests and acceptance criteria |
| Versioning | Advertised contract version and compatibility signaling | Supported-version policy in host software | Version matrix verification |
| Power management | Actual mode transitions and safety checks | Request timing and policy on retries | Power-mode transition tests |
| Reset behavior | Reset cause capture, readiness assertion, safe failure behavior | Boot sequencing expectations and recovery policy | Reset-path verification |
| Logging | Event generation, schema compliance, stable event IDs | Log ingestion, storage, and interpretation | Log schema validation |
| Error handling | Canonical status codes and state preservation rules | Reaction to errors and fallback behavior | Negative-path testing |

## 5) Assumptions
- Firmware and Host can exchange a versioned, machine-readable status structure.
- Host software is responsible for checking compatibility before enabling version-specific behavior.
- The platform has a defined monotonic time base or tick source available for logs.
- Power-mode names in this document are the canonical contract names; implementation-specific modes must map to them.
- Firmware can preserve a last-error or last-reset-cause field across the relevant lifecycle boundary.
- Validation has access to runtime observability needed to confirm returned statuses and log outputs.

## 6) Validation hooks
- **Version check test:** Verify firmware reports the expected contract version and that Host rejects unsupported versions.
- **State machine test:** Exercise `RESET -> INIT -> READY -> BUSY -> READY` and verify only allowed transitions occur.
- **Error code test:** Inject invalid parameters, unsupported requests, and busy conditions; confirm exact status codes and no unintended state change.
- **Logging test:** Confirm required log fields are present, event IDs are stable, and error logs include status/context.
- **Power-mode test:** Request each supported mode and verify returned status, resulting state, and host retry behavior.
- **Reset/readiness test:** Confirm reset cause is retained through boot and readiness is asserted only after initialization completes.
- **Compatibility regression test:** Run host against prior minor/patch firmware builds to verify no contract breakage.
- **Negative-path test:** Attempt commands before readiness, during busy periods, and in invalid states; confirm deterministic rejection.