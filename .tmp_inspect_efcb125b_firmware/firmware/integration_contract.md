# Firmware Integration Contract

## 1) Contract overview

- This contract defines the firmware-facing integration surface for the `intelligent_active_aerodynamics_controller` running on the FPGA soft CPU.
- Scope is **portable source only** for the selected board `ulx3s_ecp5_45f`; a deployable binary is **not** claimed because the soft-CPU subsystem and BSP are missing.
- Firmware responsibility is limited to **command scheduling, host-service communication, sequence management, envelope checks, and fault acknowledgment policy**.
- Safety-critical clamping and final actuator enforcement remain outside firmware ownership and belong to FPGA control/safety logic.
- Firmware consumes `wb_ctrl`, `sensor_inputs`, `audit_log`, and service responses, and produces request packets, register updates, fault clears, and telemetry.
- Freshness handling is mandatory: stale, delayed, or out-of-order updates must be rejected or downgraded per policy.
- All interactions must be traceable through `audit_log` with versioned event records and error codes.
- The contract is portable across transport selections; `host_transport` is not yet selected and therefore transport-specific details are intentionally abstracted.

## 2) Contract version + compatibility policy

**Contract version:** `chiploop.firmware.integration_contract.v1.0`

**Compatibility policy:**
- **Backward-compatible** changes are allowed when they:
  - add optional fields,
  - add new telemetry/event codes,
  - add non-breaking validation hooks,
  - preserve existing field semantics and default behavior.
- **Forward-incompatible** changes require a major version bump and re-validation of:
  - sequencing rules,
  - freshness rules,
  - fault acknowledgment behavior,
  - envelope-check outcomes,
  - audit record schema.
- Firmware must reject unknown **mandatory** fields and must ignore unknown **optional** fields if marked extensible by the upstream producer.
- Version negotiation is required at initialization and must be logged in `audit_log`.
- If version mismatch prevents safe operation, firmware must enter fallback-safe behavior and report a contract-version error.

## 3) Interfaces

### 3.1 External interface summary

| Interface | Type | Direction | Owner | Contract behavior |
|---|---|---:|---|---|
| `geometry_input` | STL geometry | input | System/Host | Preprocessed outside firmware; not parsed by firmware. |
| `operating_conditions` | structured numeric input | input | System/Host | Supplies velocity/scenario parameters; firmware uses only validated, encoded summaries if exposed via service messages. |
| `model_or_reference_output` | numeric response stream | output | System/Host | Produced by external software/GPU service; firmware consumes only as service response data. |
| `actuator_command` | bounded control command | output | FPGA control/safety logic | Firmware may request/sequence commands, but firmware does not directly own final clamping. |
| `freshness_metadata` | timestamp and sequence metadata | input | Shared | Used for stale/out-of-order rejection and sequence acceptance. |
| `safety_state` | status signal | output | FPGA control/safety logic | Firmware must report or mirror state class, not override safety enforcement. |
| `audit_log` | event trace | bidirectional | Shared | Firmware appends policy, sequencing, error, and validation events; host may read for validation. |

### 3.2 Firmware service contract

| API / Message Class | Direction | Required behavior | Error handling |
|---|---|---|---|
| `fw_init(version, board_id, transport_id)` | input | Validate contract version, board binding, and selected transport abstraction. | Reject on version mismatch or unsupported board binding. |
| `fw_schedule_request(seq, payload)` | output | Emit request packet for host-service or internal orchestration step. | Reject stale, duplicate, or out-of-order `seq`. |
| `fw_apply_response(seq, response)` | input | Accept service response only if freshness and sequence checks pass. | Log and ignore invalid response; may trigger fallback status. |
| `fw_update_registers(update_id, fields)` | output | Produce register updates for downstream control logic or soft-CPU-side registers. | Block invalid envelope fields and log error code. |
| `fw_clear_fault(fault_id, ack_policy)` | output | Request fault clear only when policy permits acknowledgment. | Deny clear request when fault is latched or policy disallows. |
| `fw_emit_telemetry(snapshot_id)` | output | Publish telemetry snapshot with sequence, freshness, and state. | Telemetry must be self-consistent or marked invalid. |
| `fw_report_status(code, detail_ref)` | output | Publish current safety/policy state and error class. | Must always be available after init. |

### 3.3 Data and state rules

| Category | Rule |
|---|---|
| Sequence management | Monotonic sequence numbers required for all externally visible request/response exchanges. |
| Freshness | Inputs older than the accepted watermark are rejected. |
| Envelope checks | Command and response payloads must remain inside approved bounds before any downstream propagation. |
| Fault acknowledgment | Fault clears are policy-driven, not automatic; firmware must consult current fault state and acknowledgment policy. |
| Telemetry | Must include version, sequence, freshness verdict, envelope verdict, and state classification. |
| Logging | Every rejection, fallback transition, clear request, and version check must be logged. |

### 3.4 Error codes

| Error code | Meaning | Action |
|---|---|---|
| `FW_OK` | Accepted and processed | Continue normal operation. |
| `FW_ERR_VERSION` | Contract version mismatch | Enter fallback-safe behavior. |
| `FW_ERR_STALE` | Input or response stale | Reject update, log event. |
| `FW_ERR_OUT_OF_ORDER` | Sequence violation | Reject message, preserve prior state. |
| `FW_ERR_ENVELOPE` | Payload outside valid bounds | Block downstream update. |
| `FW_ERR_FAULT_POLICY` | Fault clear not permitted | Deny clear request, retain latched status. |
| `FW_ERR_TRANSPORT` | Transport abstraction failure | Preserve safe state, retry per host policy. |
| `FW_ERR_INTERNAL` | Firmware internal inconsistency | Log and transition to safe fallback. |

## 4) Ownership boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| Policy sequencing | Owns sequencing decisions and request issuance | Supplies scenario context and service results | Verifies ordering and replay rejection |
| Envelope checks | Performs pre-dispatch checks against contract bounds | Supplies bound definitions and reference data | Exercises in-range / out-of-range cases |
| Freshness handling | Enforces stale/out-of-order rejection | Supplies timestamps and sequence metadata | Fuzzes age, jitter, reorder cases |
| Fault acknowledgment | Applies acknowledgment policy and clear requests | May request clear, but not authorize it | Confirms latched-fault behavior |
| Final actuation clamp | Does not own final clamp | May observe final effect only | Confirms clamp occurs in safety logic |
| Audit logging | Appends firmware decisions and errors | May read/write shared trace according to policy | Checks trace completeness and versioning |

## 5) Assumptions

- The selected board is `ulx3s_ecp5_45f`, but the soft-CPU BSP is not yet available.
- `host_transport` is intentionally unspecified and will be bound later without changing this contract’s semantic rules.
- Firmware will run on a soft CPU inside the FPGA fabric, not on an external hard CPU.
- External software/GPU services may compute reference outputs, but firmware treats them as inputs for policy and sequencing only.
- Safety-critical clamping is handled by FPGA control/safety logic, not by firmware.
- The approved partition already defines RTL collateral for register-facing interactions; this contract only defines firmware behavior against that collateral.
- A deployable firmware image is out of scope until the platform contract gate is ready.

## 6) Validation hooks

- **Version negotiation test:** Verify firmware rejects unsupported contract versions and logs `FW_ERR_VERSION`.
- **Sequence monotonicity test:** Send duplicated, skipped, and reversed sequence numbers; verify rejection and unchanged downstream state.
- **Freshness test:** Inject stale timestamps and delayed responses; verify stale rejection and audit logging.
- **Envelope test:** Provide in-bound and out-of-bound command payloads; verify only valid payloads produce register updates or request packets.
- **Fault policy test:** Attempt fault clear under allowed and disallowed policies; verify correct acceptance/denial and trace entry.
- **Telemetry consistency test:** Ensure every telemetry snapshot includes version, sequence, freshness verdict, and safety state.
- **Audit completeness test:** Confirm each rejection, fallback transition, and clear request generates a trace record.
- **Fallback behavior test:** Force internal inconsistency or transport failure; verify safe fallback state is reported and preserved.
- **Boundary test with host/software:** Confirm firmware does not parse STL geometry directly and does not own final actuator clamping.