# Firmware Integration Contract — intelligent_active_aerodynamics_controller

## Contract overview
- This contract defines the firmware-facing integration for the PicoRV32 soft CPU subsystem on the `ulx3s_ecp5_45f` FPGA prototype, using the approved partition and existing RTL register collateral.
- Firmware scope is limited to control-loop orchestration, request packaging, response handling, CSR management, fault acknowledgment, and telemetry/observability.
- The firmware consumes the Wishbone CSR map plus request/response stream interfaces and produces actuator commands, fault clear actions, and structured logs.
- The system operates in soft real-time against the 50 MHz control domain and watchdog deadlines; firmware must treat freshness and timeout status as first-class runtime conditions.
- The deployment posture is `portable_only`; a deployable binary is not claimed because the `soft_cpu_subsystem_and_bsp` platform gate is still missing.
- System/host software owns configuration intent, build/deployment orchestration, and post-run analysis; firmware owns in-target execution and local safety handling.
- Validation must prove register compatibility, request/response semantics, fault handling, and safe fallback behavior before any binary is considered release-eligible.
- No claim is made for external transport selection, power-management features, or interrupt/DMA architecture beyond the specified interfaces and contract scope.

## Contract version + compatibility policy
- **Contract version:** `1.0.0-portable`
- **Compatibility policy:** semantic compatibility for firmware-visible register fields, stream message fields, status meanings, and fault codes.
- **Breaking changes require:** a major version bump, updated RTL collateral, and re-validation of all firmware/host integration tests.
- **Backward-compatible changes:** additive telemetry fields, new non-conflicting CSR bits, and optional status flags that preserve existing meanings.
- **Binary compatibility is not implied:** source-level compatibility is the current target; deployable firmware binary readiness remains blocked by the missing platform gate.

## Interfaces

### Firmware-facing interface summary

| Interface | Type | Direction | FW Role | Notes |
|---|---|---:|---|---|
| `geometry_input` | STL | In | Consume | Used by higher-level system flow; not parsed by low-level control firmware unless explicitly staged by host-side tooling. |
| `stream_velocity_input` | scalar_mps | In | Consume | Used for control-law context and observability. |
| `control_command_output` | actuator_setpoint | Out | Produce | Final actuator setpoint emitted by firmware after validation and fallback checks. |
| `freshness_status` | status_signal | Out | Produce | Indicates whether request/response/control state remains within freshness bounds. |
| `timeout_status` | status_signal | Out | Produce | Indicates watchdog/response timeout condition. |
| `safe_fallback_state` | state_signal | Out | Produce | Indicates firmware has transitioned to safe fallback mode. |
| `reference_log` | structured_log | Out | Produce | Structured telemetry and error records for host/validation consumption. |
| `wb_ctrl` | Wishbone slave | In/Out | Consume/Drive | CSR access for control, configuration, status, and fault acknowledgment. |
| `wb_timer` | Wishbone slave | In/Out | Consume/Drive | Timer/watchdog configuration and elapsed-time status. |
| `aero_req_stream` | streaming request interface | Out | Produce | Request packaging and launch toward the control pipeline. |
| `aero_rsp_stream` | streaming response interface | In | Consume | Response handling and completion/error decode. |
| `actuator_out` | actuator command port | Out | Produce | Hardware-facing actuator command emission. |
| `fault_out` | status fault output | Out | Produce | Latched fault indication to the surrounding system. |

### Wishbone/stream contract behaviors

| Interface | Expected behavior | Error handling | Persistence |
|---|---|---|---|
| `wb_ctrl` | Supports CSR reads/writes for enable, mode, request launch, status, fault ack, and telemetry snapshot control. | Invalid accesses return bus error or are ignored per RTL-defined CSR behavior; firmware must not assume side effects on invalid writes. | Control bits persist until explicitly changed or reset. |
| `wb_timer` | Configures freshness/watchdog thresholds and exposes timeout status. | Out-of-range timer values must be clamped or rejected according to RTL collateral; firmware must log the outcome. | Timer settings persist across normal run until reprogrammed. |
| `aero_req_stream` | Firmware emits well-formed requests only when input state is fresh and control is enabled. | If request packaging fails, firmware must suppress launch and enter safe fallback if the failure is safety-relevant. | Request launch is event-driven, not continuously asserted. |
| `aero_rsp_stream` | Firmware consumes responses, validates sequence/format, and updates control state or faults. | Malformed/late responses must be logged and treated as timeout/freshness events. | Response state is transient; only derived status is retained. |
| `actuator_out` | Outputs the current actuator setpoint or fallback setpoint. | On fault or timeout, output must transition to safe fallback state. | Holds last valid command only while freshness remains valid. |
| `fault_out` | Reflects latched fault condition. | Clears only on explicit firmware fault-ack action when safe to do so. | Latches until acknowledged or reset per RTL policy. |

### Host-visible logging schema

| Field | Type | Meaning |
|---|---|---|
| `timestamp` | u64 | Local control-domain time or tick count. |
| `event_id` | u32 | Stable event code for firmware/host correlation. |
| `severity` | enum | `info`, `warn`, `error`, `fault`. |
| `subsystem` | string | Logical origin, e.g. `wb_ctrl`, `wb_timer`, `req_mgr`, `rsp_mgr`, `safety`. |
| `detail_code` | u32 | Contracted code for specific condition. |
| `state_before` | struct | Snapshot of relevant control state before action. |
| `state_after` | struct | Snapshot of relevant control state after action. |

### Error code policy

| Code range | Meaning | Ownership |
|---|---|---|
| `0x0000` | Success / no error | Shared |
| `0x0001-0x00FF` | Firmware-defined recoverable conditions | Firmware |
| `0x0100-0x01FF` | Timeout/freshness/watchdog conditions | Firmware |
| `0x0200-0x02FF` | Response format/sequence violations | Firmware |
| `0x0300-0x03FF` | Fault-latched / safe fallback conditions | Firmware |
| `0x8000-0xFFFF` | RTL/host integration or reserved platform errors | System/Host + Validation |

## Ownership boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| CSR programming | Implements runtime reads/writes and state updates | Defines desired configuration and launch policy | Verifies register map fidelity |
| Request/response handling | Packages requests, validates responses, drives state machine | Provides input intent and end-to-end scenario definitions | Checks message format and timing |
| Fault acknowledgment | Performs safe ack only when conditions permit | Requests recovery or restart policy | Confirms fault latch/clear semantics |
| Telemetry/logging | Emits structured logs and status codes | Collects and analyzes logs | Checks schema and completeness |
| Safe fallback | Enforces local fallback transition | Consumes fallback indication | Validates fallback activation timing |
| Binary packaging | Not responsible for platform bring-up artifacts | Owns build/deploy orchestration once gate is available | Confirms reproducibility and release criteria |

## Assumptions
- The RTL CSR map and stream field definitions are already approved and stable enough for source integration.
- The PicoRV32 soft CPU subsystem exists logically in the architecture but the BSP/platform gate is not yet complete.
- Firmware has access to a local timer source via `wb_timer` sufficient for freshness and timeout enforcement.
- The host/system layer can provide or collect `reference_log` records for validation and traceability.
- Safe fallback is a defined actuator state in the RTL/control collateral, even if its exact numeric encoding is platform-specific.
- No DMA, interrupt, or power-mode contract is asserted here because they were not requested in the user scope.
- The firmware must not assume any external transport selection beyond the provided Wishbone and stream interfaces.

## Validation hooks
- **CSR map conformance test:** verify every documented control/status bit and field can be read, written, and observed with the expected reset values and persistence.
- **Request packaging test:** inject known control inputs and confirm `aero_req_stream` emits the exact expected request fields and ordering.
- **Response handling test:** feed valid, late, truncated, and malformed responses; confirm correct state transitions, logging, and fault behavior.
- **Freshness/timeout test:** vary `wb_timer` thresholds and input arrival times to confirm `freshness_status`, `timeout_status`, and fallback transitions.
- **Fault acknowledgment test:** assert fault conditions and verify latched `fault_out`, clear sequencing, and prevention of unsafe command release.
- **Telemetry schema test:** inspect `reference_log` records for required fields, stable event IDs, and correct severity/detail coding.
- **Reset/recovery test:** confirm reset returns the firmware to known-safe defaults and does not emit actuator commands before initialization is complete.
- **Integration replay test:** run a captured request/response trace through the firmware and compare output commands, status signals, and logs against expected golden behavior.