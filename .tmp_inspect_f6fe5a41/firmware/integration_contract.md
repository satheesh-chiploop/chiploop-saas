# firmware/integration_contract.md

## Contract overview
- Target platform is **portable-only** for **`ulx3s_ecp5_45f`** in an **`fpga_soft_cpu`** deployment architecture.
- Firmware scope is the **embedded control contract** for `intelligent_active_aerodynamics_controller`, not a deployable binary.
- Platform gate is **not ready**: `portable_source_ready = true`, `deployable_binary_ready = false`, missing **`soft_cpu_subsystem_and_bsp`**.
- Firmware owns **command validation, clamping, freshness checks, fallback entry, telemetry emission, and register-level control/status** through `wb_ctrl`.
- Host/System software owns **geometry ingestion, surrogate execution plumbing where applicable, log collection, and higher-level policy selection**.
- Validation must be deterministic and audit-friendly via `reference_trace` and `telemetry_log`.
- Output commands to actuation are **bounded** and must only be marked valid when freshness, safety, and state checks pass.
- Safety reporting must be surfaced through `safety_feedback` and interrupt signaling via `status_irq` when the soft CPU subsystem exists.

## Contract version + compatibility policy
**Contract version:** `1.0.0-portable`

**Compatibility policy**
- **Backward-compatible changes**:
  - adding optional telemetry fields,
  - adding non-breaking status bits,
  - extending debug-only logs,
  - adding new register fields with reserved-bit preservation.
- **Breaking changes** require a **major version bump**:
  - changing signal widths,
  - changing command encoding,
  - changing validity semantics,
  - changing timeout/freshness policy,
  - changing clamp/fallback behavior.
- Firmware must treat unknown reserved bits as **zero-ignored** on input and **preserve-as-zero** on output.
- Host/System software must not assume deployability until the **platform contract gate** reports `deployable_binary_ready = true`.

## Interfaces

### 1) Functional interfaces

| Interface | Type | Fields / Width | Firmware contract behavior |
|---|---:|---|---|
| `geometry_input` | file_or_stream | STL | Accept reference geometry for offline/validation processing. Firmware does not own parsing; it consumes only validated geometry-derived metadata if provided by host. |
| `operating_state_input` | structured_input | `stream_velocity_mps`, `system_state`, `control_context`, `input_timestamp` | Use as primary runtime input for command selection and freshness checks. Reject stale or malformed state. |
| `control_output` | structured_output | `actuator_command`, `command_valid`, `command_timestamp`, `fallback_state` | Emit bounded actuator command word, validity flag, timestamp, and fallback indicator. |
| `safety_feedback` | event_channel | `stale_data_detected`, `timeout_detected`, `clamp_applied`, `fallback_entered` | Emit supervision events when freshness fails, command timing expires, clamping occurs, or fallback is entered. |
| `reference_trace` | data_log | `inputs`, `intermediate_states`, `reference_outputs`, `timestamps` | Provide deterministic traceability for validation and audit. |
| `telemetry_log` | data_log | `control_decisions`, `validity_flags`, `limit_events`, `error_metrics`, `fallback_events` | Provide runtime observability for verification and post-run analysis. |
| `surrogate_req_stream` | valid_ready_stream | 128 bits | Compact request transport between FPGA control plane and software/GPU surrogate execution. Firmware must not assume external latency bounds beyond configured timeout. |
| `surrogate_rsp_stream` | valid_ready_stream | 128 bits | Compact response transport from surrogate/reference execution back to FPGA control plane. |
| `wb_ctrl` | wishbone | N/A | Soft CPU control/status access for firmware-managed configuration, arming, and telemetry. |
| `actuator_cmd_out` | compact_parallel | 32 bits | Registered, clamped actuator command word to downstream actuation hardware. |
| `status_irq` | interrupt | 1 bit | Signal stale-data, timeout, response-ready, or fault transitions to soft CPU when available. |
| `uart` | uart | 2 bits | Optional debug and telemetry path for soft CPU subsystem. |

### 2) Control semantics

| Signal / Object | Required behavior | Failure handling |
|---|---|---|
| `actuator_command` | Must be clamped to firmware-defined bounds before assertion. | On out-of-range input, set `clamp_applied=1`, set `command_valid=0` if policy requires invalidation, and enter fallback if persistent. |
| `command_valid` | Assert only when state freshness, control context, and policy checks pass. | Deassert on stale, timeout, or invalid state. |
| `command_timestamp` | Must reflect the accepted decision time or sample time used by firmware policy. | If timestamp is absent or older than freshness window, mark stale. |
| `fallback_state` | Indicates firmware is using degraded or safe default behavior. | Must be asserted on timeout, invalid inputs, or repeated safety violations. |
| `stale_data_detected` | Raised when `input_timestamp` exceeds freshness window. | Causes invalidation and telemetry event emission. |
| `timeout_detected` | Raised when expected response or update deadline is exceeded. | Causes fallback entry per policy. |
| `clamp_applied` | Raised when command is limited to safe bounds. | Must be logged in `telemetry_log.limit_events`. |
| `fallback_entered` | Raised when safe fallback mode is entered. | Must be latched until cleared by explicit policy/action. |

### 3) WB control/status contract

| Category | Contract requirement |
|---|---|
| Ownership | Firmware owns runtime interpretation; host/system owns provisioning of policy values and reading status. |
| Register access | All writable controls are software-mediated via `wb_ctrl`; readback must reflect latched state and safety flags. |
| Determinism | Register writes must produce deterministic state transitions with no hidden side effects. |
| Reserved bits | Must be written as zero and ignored on read unless defined in a future version. |
| Telemetry access | Telemetry snapshots may be polled or drained through control/status registers as implemented by the BSP. |
| Reset behavior | Reset shall restore safe defaults: command invalid, fallback-safe state, no armed actuation. |

## Ownership boundaries

| Area | Firmware (FW) | System/Host | Validation |
|---|---|---|---|
| Command generation | Implements bounded command decision and fallback logic | Supplies policy, context, and upstream inputs | Checks command bounds and validity transitions |
| Geometry handling | Consumes validated geometry metadata only | Parses STL and prepares reference geometry artifacts | Verifies geometry-to-command traceability |
| Freshness / timeout policy | Enforces runtime checks | Defines freshness thresholds and update cadence | Stresses stale and timeout cases |
| Register access (`wb_ctrl`) | Implements control/status semantics | Reads/writes configuration and status | Confirms register map behavior |
| Logging | Emits runtime telemetry and trace hooks | Collects and archives logs | Confirms schema completeness and ordering |
| Safety events | Raises safety feedback and fallback state | Consumes events for supervisory action | Injects fault conditions and checks event delivery |

## Assumptions
- The soft CPU subsystem and BSP are **not yet available**, so this contract defines behavior but not a final binary integration.
- STL geometry is provided by the host or validation toolchain; firmware does not perform full CAD parsing.
- A finite command clamp range exists and will be defined in the BSP/register map, but its exact numeric bounds are not yet fixed in the provided collateral.
- `surrogate_req_stream` and `surrogate_rsp_stream` are present for cooperative execution or reference computation; they are not assumed mandatory for all control cycles.
- `status_irq` is available only after the soft CPU subsystem is integrated.
- UART use is optional and must not be required for safety or control correctness.
- Logging sinks may be memory-backed, streamed, or host-drained depending on BSP integration.

## Validation hooks
- **Register conformance tests**: verify `wb_ctrl` read/write behavior, reserved-bit handling, reset defaults, and state latching.
- **Freshness tests**: inject old `input_timestamp` values and confirm `stale_data_detected`, invalidation, and fallback behavior.
- **Timeout tests**: hold back surrogate responses or control updates and confirm `timeout_detected` and safe fallback entry.
- **Clamp tests**: force command requests outside bounds and verify `clamp_applied` plus bounded `actuator_cmd_out`.
- **Trace determinism tests**: replay identical input sequences and compare `reference_trace` and `telemetry_log` for stable ordering and content.
- **Safety event tests**: validate `safety_feedback` emission for stale, timeout, clamp, and fallback transitions.
- **Interface contract tests**: confirm width, field names, and presence/absence semantics for all declared interfaces.
- **Gate-readiness tests**: block deployable binary generation until `soft_cpu_subsystem_and_bsp` is present and the platform gate reports ready.