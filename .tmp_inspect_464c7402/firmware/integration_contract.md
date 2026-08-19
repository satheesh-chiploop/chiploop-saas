# Firmware Integration Contract — intelligent_active_aerodynamics_controller

## 1) Contract overview
- This contract defines the firmware-side integration boundary for the active-aerodynamics control path on the approved portable target: `ulx3s_ecp5_45f`, deployment architecture `fpga_soft_cpu`.
- Firmware owns deterministic control decision generation, command clamping/supervision, service watchdog handling, stale-response rejection, and telemetry record emission.
- Host/software owns surrogate execution, reference computation, geometry preparation, and any non-deterministic or compute-heavy processing not resident in the soft CPU.
- The firmware control loop shall only act on validated inputs: velocity within range, fresh model response, valid comparison results, and configured safe limits.
- No deployable binary is implied by this contract; platform bring-up remains gated by the missing soft CPU subsystem and BSP.
- All external service interactions use bounded request/response packets with explicit sequence, freshness, and timeout checks.
- Safe fallback behavior is mandatory on deadline miss, stale data, sequence mismatch, or invalid configuration.
- Telemetry must be traceable, non-blocking, and suitable for validation/debug without stalling the control loop.

## 2) Contract version + compatibility policy
**Contract version:** `1.0.0`  
**Schema:** `chiploop.application_intelligence.target_refinement.v1`

**Compatibility policy**
- **Backward-compatible within minor versions:** added optional fields, added telemetry keys, and new non-breaking status codes may be introduced without breaking existing firmware consumers.
- **Breaking changes require major version increment:** changes to packet layout, field semantics, command range conventions, or status meaning require `MAJOR` bump.
- **Firmware shall reject unknown required fields or incompatible packet versions** when version negotiation is present.
- **Host/system software must not assume binary compatibility** unless both contract version and packet version match exactly.
- **Portable source is ready; deployable binary is not ready** until the soft CPU subsystem and BSP are integrated.

## 3) Interfaces

### 3.1 Input interfaces
| Name | Type | Direction | Ownership | Contract behavior |
|---|---|---:|---|---|
| `stl_geometry_input` | file_or_blob | in | System/Host | Geometry source derived from DrivAerML reference geometry. Firmware does not parse STL in the control loop; if used, host pre-processes into a compact form before control runtime. |
| `velocity_input` | scalar | in | System/Host or sensor front-end | Valid only in range `20..55 m/s`. Out-of-range values are rejected and force safe fallback policy per configuration. |
| `configuration_input` | registers_and_params | in | System/Host, persisted/consumed by FW | Provides safe command limits, freshness thresholds, timeout thresholds, mode settings, and supervision policy. Firmware treats as authoritative once validated. |
| `model_response_packet` | bounded_stream | in | System/Host | Contains surrogate prediction and status. Must include sequence/freshness data sufficient for stale rejection and timeout handling. |
| `reference_output` | software_result | in | Validation/System | Baseline aerodynamic result for comparison. Not required in closed-loop runtime unless validation mode is enabled. |

### 3.2 Output interfaces
| Name | Type | Direction | Ownership | Contract behavior |
|---|---|---:|---|---|
| `model_request_packet` | bounded_stream | out | Firmware | Compact request from control firmware to external surrogate service. Must be bounded, deterministic, and sequence-tagged. |
| `comparison_metrics` | status_or_struct | out | Firmware | Deviation metrics and accept/reject result against reference implementation. Emitted when comparison data is available. |
| `actuator_command` | scalar_control | out | Firmware | Bounded active-aerodynamics command after clamping and supervision. Final command is safe-limited before output. |
| `stale_rejection_status` | status | out | Firmware | Asserted when response is stale, mismatched, or fails freshness policy. |
| `timeout_fault_status` | status | out | Firmware | Asserted on deadline miss or service silence detected by watchdog logic. |
| `safe_fallback_indicator` | status | out | Firmware | Indicates system is in safe fallback mode; command is driven to configured safe value or hold policy. |
| `telemetry_record` | log_stream | out | Firmware | Traceable diagnostics and decision history; background priority only. |

### 3.3 Control packet contract
| Field | Type | Direction | Requirement |
|---|---|---:|---|
| `packet_version` | u16 | both | Required for compatibility checking. |
| `sequence_id` | u32 | both | Required for stale/mismatch detection. |
| `timestamp_or_age` | u32/u64 | both | Required for freshness policy enforcement. |
| `mode_id` | enum | both | Required to distinguish manual/auto/validation/fallback modes. |
| `velocity_mps` | scalar | req | Must be within `20..55` on accepted control path. |
| `command_limit_min` | scalar | cfg | Required safe lower bound. |
| `command_limit_max` | scalar | cfg | Required safe upper bound. |
| `prediction_payload` | compact struct | resp | Required when model response is valid. |
| `status_code` | enum | resp | Required for acceptance/rejection outcome. |
| `comparison_payload` | compact struct | out | Optional; emitted when reference comparison is active. |

### 3.4 Error/status codes
| Code | Meaning | Owner |
|---|---|---|
| `OK` | Accepted and processed | Firmware |
| `INVALID_CONFIG` | Configuration rejected as unsafe or malformed | Firmware |
| `OUT_OF_RANGE_VELOCITY` | Velocity outside allowed range | Firmware |
| `STALE_RESPONSE` | Response age exceeded freshness threshold | Firmware |
| `SEQUENCE_MISMATCH` | Response sequence does not match request | Firmware |
| `TIMEOUT` | Service deadline miss or silence detected | Firmware |
| `SAFE_FALLBACK_ACTIVE` | Fallback policy currently enforced | Firmware |
| `COMPARISON_REJECTED` | Prediction/reference deviation exceeds policy | Firmware |
| `INTERNAL_FAULT` | Unspecified firmware fault; conservative fallback required | Firmware |

### 3.5 Power-mode policy
| Mode | Firmware behavior | Host behavior |
|---|---|---|
| Active control | Full deterministic control loop enabled | Supplies model service and optional validation inputs |
| Safe fallback | Command constrained to safe value/hold policy; telemetry continues | May be notified of fault/fallback state |
| Low-power idle | Control loop paused if permitted by system mode; state retained if supported | Must not expect command updates until ready signal |
| Boot/init | Sanity checks, config validation, readiness gating | May stage configuration and model service connectivity |

## 4) Ownership boundaries
| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| Control decision generation | Owns bounded decision formation and command clamping | Supplies inputs only | Verifies outputs against expected policy |
| Model request/response transport | Owns packet formation, acceptance checks, watchdogs | Owns surrogate service implementation and transport endpoint | Injects timing/sequence faults |
| Reference comparison | Owns accept/reject decision from received metrics | Owns reference computation | Confirms deviation thresholds and baselines |
| Telemetry | Owns record emission and local traceability | May collect/export records | Checks schema completeness and ordering |
| Geometry handling | Uses preprocessed geometry metadata only as needed for runtime | Owns STL ingestion/preprocessing | Validates geometry-derived inputs |
| Safety fallback | Owns fallback activation and command suppression | May observe status | Verifies deterministic safe-state entry |

## 5) Assumptions
- The soft CPU subsystem and BSP are not yet available, so this contract is integration-ready but not deployable.
- Firmware control-loop timing is deterministic once the platform contract gate is satisfied.
- STL input is not processed directly in the time-critical loop; host-side preprocessing or offline conversion is assumed.
- Velocity input is authoritative only when within `20..55 m/s`; outside this range the control path shall not issue a normal command.
- Safe command limits are provided via configuration and are valid only after firmware validation.
- Comparison with `reference_output` is a validation-mode or supervisory feature and may be absent in normal closed-loop operation.
- Telemetry must be non-blocking and may be dropped or summarized if necessary to protect the control loop.
- No interrupt, DMA, or boot-only-specific contract details are included because they were not requested in scope.

## 6) Validation hooks
- **Version check:** Verify packet version negotiation and reject incompatible major versions.
- **Range enforcement:** Inject velocities below 20 m/s and above 55 m/s; confirm rejection and safe fallback.
- **Freshness test:** Delay `model_response_packet` beyond configured threshold; confirm `stale_rejection_status` and/or `timeout_fault_status`.
- **Sequence test:** Replay an old response with mismatched `sequence_id`; confirm rejection.
- **Command clamp test:** Provide out-of-range candidate commands; confirm final `actuator_command` is clamped to safe limits.
- **Comparison gate test:** Feed reference deviation above threshold; confirm `COMPARISON_REJECTED` and fallback behavior if configured.
- **Telemetry schema test:** Confirm each emitted `telemetry_record` contains sequence, mode, status, timing, and decision fields required by the logging schema.
- **Fault recovery test:** Force service silence and validate deterministic transition into `safe_fallback_indicator` without control-loop blockage.
- **Readiness gate test:** Confirm firmware does not advertise deployability until `soft_cpu_subsystem_and_bsp` is present and initialized.
- **Traceability test:** Correlate request, response, comparison, and command records by `sequence_id` across runtime logs.