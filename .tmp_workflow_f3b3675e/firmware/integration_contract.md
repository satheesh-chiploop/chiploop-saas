# Firmware Integration Contract — intelligent_active_aerodynamics_controller

## 1) Contract overview
- Firmware is responsible for control-policy orchestration, command packing, freshness/validity checks, and safe fallback decisions before handing commands to the FPGA control plane.
- The target deployment is **portable-only** on **ulx3s_ecp5_45f** with **fpga_soft_cpu** architecture; **deployable binary is not ready** because the soft CPU subsystem and BSP are missing.
- Firmware consumes validated operating condition data, surrogate/reference prediction metadata, and fault/fallback inputs, then emits compact bounded actuator commands.
- The control path must remain deterministic and bounded by the control-cycle deadline; command generation must be shorter than model runtime.
- All actuator commands exposed to FPGA must be compact, 32-bit maximum, clamped, and qualified by valid/ready semantics.
- Status reporting must cover freshness, validity, timeout, clamp events, fallback activation, and command acceptance/rejection.
- Auditability is required: firmware decisions must be reconstructable from logged inputs, policy decisions, and output command descriptors.
- Host/system software owns model execution, preprocessing, and log collection; firmware owns policy execution and register-level orchestration.

## 2) Contract version + compatibility policy
**Contract version:** `1.0.0`

**Compatibility policy**
- **Major version** changes indicate breaking interface or behavior changes in command packing, status semantics, or register map.
- **Minor version** changes add backward-compatible fields, status bits, or optional metadata.
- **Patch version** changes correct behavior without changing observable interface semantics.
- Firmware must reject incompatible host/software metadata versions if command interpretation would be ambiguous.
- Unknown optional fields must be ignored unless explicitly marked mandatory for the active control mode.
- Register layout and command bit allocations are stable within a major version.

## 3) Interfaces

### 3.1 Functional interface summary

| Interface | Direction | Owner | Purpose | Notes |
|---|---:|---|---|---|
| `operating_condition_input` | in | FW/System | Structured numeric control inputs | Validated for 20–55 m/s envelope before control use |
| `surrogate_prediction_output` | out | SW/GPU service | Predicted aerodynamic quantities | Firmware consumes metadata/summary, not raw model execution |
| `reference prediction output` | in | SW | Reference comparison input | Used in policy logic and fallback decisions |
| `fault_and_fallback_input` | in | FW/FPGA | Fault indicators or supervisory fallback trigger | Forces deterministic degraded mode |
| `actuator_command_output` | out | FPGA | Bounded control vector | Compact packed bus with valid/ready handshake |
| `status_and_health_output` | out | FPGA/SW | Health, freshness, timeout, validity, fallback reporting | Aggregated for control-plane and software consumption |
| `wb_ctrl` | inout | FPGA | Wishbone control/status register window | 32-bit compact register-mapped interface |
| `irq` | out | FPGA | Event signaling | Indicates accepted command, stale rejection, timeout, invalid input, clamp event, or safe fallback entry |
| `actuator_cmd` | out | FPGA | Packed actuator target command bus | Width must not exceed 32 bits |
| `actuator_valid` | out | FPGA | Command qualifier | Registered output |
| `actuator_ready` | in | FPGA | Downstream backpressure | No bulk FIFO may be inferred |
| `fault_safe` | out | FPGA | Safe fallback indication | Latched until cleared by policy/acknowledgment |

### 3.2 Register-level control contract

| Register / Field | Access | Width | Semantics |
|---|---:|---:|---|
| `CTRL_MODE` | RW | 2 | Selects normal, degraded, or safe fallback control mode |
| `SEQ_IN` | RW | 16 | Sequence number for compact command correlation |
| `CMD_WORD` | WO | 32 | Packed bounded actuator command descriptor |
| `CMD_VALID` | WO | 1 | Strobes a new command submission |
| `STATUS` | RO | 32 | Freshness, validity, clamp, timeout, fallback, accept/reject flags |
| `FAULT_IN` | RO/WI | 32 | Latched supervisory fault and fallback indicators |
| `ACK` | WO | 1 | Acknowledges interrupt and clears sticky event indicators where permitted |

### 3.3 Command behavior contract

| Behavior | Requirement |
|---|---|
| Bounded output | Firmware must clamp all actuator fields before commit |
| Sequence tracking | Every committed command must carry a monotonically increasing sequence number within the active session |
| Freshness gating | Commands older than the freshness threshold must be rejected or forced into safe fallback, per policy |
| Validity gating | Invalid operating-condition input or missing prediction metadata must prevent normal-mode command commit |
| Fallback behavior | On fault trigger, firmware must emit deterministic safe fallback command and assert `fault_safe` |
| Acceptance semantics | A command is considered committed only when `actuator_valid=1` and `actuator_ready=1` in the same qualified transaction |

### 3.4 Logging schema

| Field | Type | Meaning |
|---|---|---|
| `timestamp` | u64 | Capture time in control-cycle units or system timebase |
| `seq_in` | u16 | Submitted sequence number |
| `ctrl_mode` | enum | Control mode selected by firmware |
| `input_validity` | bitmask | Validity and freshness checks result |
| `fault_flags` | bitmask | Active fault or fallback indicators |
| `cmd_word` | u32 | Packed actuator command |
| `clamp_flags` | bitmask | Which fields were clamped |
| `status_code` | enum | Accepted, rejected, stale, invalid, timeout, fallback |

### 3.5 Error codes

| Code | Meaning |
|---|---|
| `OK` | Command accepted and committed |
| `ERR_INVALID_INPUT` | Input out of bounds or malformed |
| `ERR_STALE_DATA` | Prediction or context data not fresh enough |
| `ERR_TIMEOUT` | Control-cycle deadline exceeded |
| `ERR_CLAMPED` | Output was clamped before commit |
| `ERR_FALLBACK` | Safe fallback mode entered |
| `ERR_BUSY` | Downstream not ready for commit |
| `ERR_VERSION_MISMATCH` | Incompatible contract version detected |

## 4) Ownership boundaries

| Area | Firmware | System/Host software | Validation |
|---|---|---|---|
| Prediction execution | No | Yes | Verifies metadata provenance |
| Geometry preprocessing | No | Yes | Confirms structured geometry handling |
| Control policy and command packing | Yes | No | Tests boundedness and determinism |
| Register access / commit handshake | Yes | No | Exercises Wishbone and valid/ready paths |
| Model comparison / analytics | No | Yes | Verifies traceability and log completeness |
| Safe fallback entry | Yes | Supervisory inputs only | Confirms deterministic fallback behavior |
| Audit log collection | Emits structured events | Aggregates and stores | Checks reconstructability and schema compliance |

## 5) Assumptions
- The selected platform remains **ulx3s_ecp5_45f** unless a new board contract is issued.
- The soft CPU BSP is not yet available; therefore no deployable binary is claimed.
- Surrogate prediction execution remains in software/GPU service; firmware consumes metadata and summarized results only.
- Control inputs are validated into the 20–55 m/s operating envelope before firmware command commit.
- No bulk FIFO is inferred on the actuator interface.
- The host/software layer will provide freshness and validity metadata in a deterministic format.
- The FPGA control plane exposes the register window and handshake semantics described above.

## 6) Validation hooks
- **Register compliance test:** Read/write all defined Wishbone registers and verify access permissions, reset values, and sticky bit behavior.
- **Command packing test:** Feed representative operating conditions and verify packed `CMD_WORD` matches the expected bit allocation and clamp policy.
- **Freshness rejection test:** Inject stale prediction/context metadata and confirm rejection or fallback per policy.
- **Fault fallback test:** Assert `fault_and_fallback_input` and verify `fault_safe`, fallback command emission, and interrupt assertion.
- **Handshake test:** Hold `actuator_ready=0` and verify no command commit occurs; then assert ready and confirm one qualified commit.
- **Sequence monotonicity test:** Submit ordered commands and verify `SEQ_IN` increments monotonically within the active session.
- **Timeout test:** Stall command submission past the control-cycle budget and verify `ERR_TIMEOUT` behavior.
- **Version compatibility test:** Present mismatched contract version metadata and confirm rejection with `ERR_VERSION_MISMATCH`.
- **Log reconstruction test:** Rebuild a control decision from audit logs and confirm the reconstructed command and status match the observed outputs.