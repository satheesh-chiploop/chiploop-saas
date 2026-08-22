# Firmware Integration Contract: intelligent_active_aerodynamics_controller

## Contract overview
- This contract defines the firmware-facing integration boundary for the `intelligent_active_aerodynamics_controller` on `ulx3s_ecp5_45f_esp32`.
- Host platform is ESP32 running ESP-IDF; fabric link to FPGA is SPI register transport, mode 0, MSB-first, max 10 MHz.
- Firmware shall own command validation, clamping, freshness checking, fallback signaling, and transaction framing for the approved MMIO/register path.
- FPGA shall expose the registered control/status surface through the specified SPI frame contract and downstream `actuator_cmd_out` / `host_irq` outputs.
- The firmware shall not claim a deployable binary is operational unless the platform contract gate is ready; this refinement marks the gate as ready.
- Streaming command ingress/egress is optional at the system level, but the approved transport contract is the SPI register path described below.
- All command commits are edge-triggered by CS rising per the transaction model; response N is observed in frame N+2.
- Auditability is required: inputs, validation result, decision path, and emitted command values shall be recorded in `trace_log`.

## Contract version + compatibility policy
- **Contract schema**: `chiploop.application_intelligence.target_refinement.v1`
- **Contract version**: `1.0.0`
- **Compatibility policy**:
  - Minor revisions may add non-breaking fields, status codes, or log keys.
  - Patch revisions may clarify behavior without changing bit mappings, timing, or ownership.
  - Any change to SPI frame size, bit offsets, response latency, or command semantics is **breaking** and requires a new major version.
  - Firmware must reject or flag unsupported contract revisions rather than silently remapping fields.

## Interfaces

### Host / FPGA transport contract

| Field | Value |
|---|---|
| Transport | SPI mode 0, MSB-first, full-duplex |
| SPI clock max | 10 MHz |
| Minimum interframe delay | 1 us |
| Frame size | 200 bits |
| Frame bytes | 25 |
| Command leading padding | 28 bits |
| Response trailing padding | 4 bits |
| Response latency | 2 frames |
| Commit semantics | Command N commits when CS rises; response N is read in frame N+2 |

### Input frame bit map

| LSB | Width | Field |
|---:|---:|---|
| 0 | 8 | `mmio_addr` |
| 8 | 32 | `mmio_wdata` |
| 40 | 1 | `mmio_write` |
| 41 | 1 | `mmio_valid` |
| 42 | 1 | `model_req_ready` |
| 43 | 128 | `model_rsp_data` |
| 171 | 1 | `model_rsp_valid` |

### Output frame bit map

| LSB | Width | Field |
|---:|---:|---|
| 0 | 1 | `host_irq` |
| 1 | 32 | `actuator_cmd_out` |
| 33 | 1 | `model_rsp_ready` |
| 34 | 1 | `model_req_valid` |
| 35 | 128 | `model_req_data` |
| 163 | 1 | `mmio_ready` |
| 164 | 32 | `mmio_rdata` |

### Functional interface mapping

| Interface name | Type | Direction | Contract role |
|---|---|---|---|
| `geometry_input` | `STL` | input | Vehicle surface geometry for preprocessing and downstream aerodynamic evaluation |
| `stream_velocity_input` | `scalar_mps` | input | Freestream velocity in 20 to 55 m/s envelope |
| `model_or_reference_state` | `structured_state` | input | Timestamped state metadata with sequence/freshness indicators |
| `control_command` | `bounded_actuator_command` | output | Validated and clamped actuator command set |
| `freshness_status` | `status_flag` | output | Indicates outputs and control inputs are current enough for use |
| `fault_or_fallback_state` | `status_flag` | output | Indicates timeout, stale-data, invalid-input, or runtime-fault fallback activation |
| `trace_log` | `audit_record` | output | Audit trail of inputs, decision path, validation, and emitted commands |
| `cpu_control_window` | `memory_mapped_registers` | inout | FPGA host interface for configuration, status, sequence tracking, watchdog control |
| `cmd_stream_in` | `valid_ready_stream` | in | Optional bounded command ingress stream for compact packets from host software to FPGA safety logic |
| `resp_stream_out` | `valid_ready_stream` | out | Optional bounded response stream carrying acceptance, clamp, timeout, and fallback status |
| `actuator_cmd_out` | `parallel_control` | out | Quantized actuator command bus to downstream actuator control |
| `host_irq` | `interrupt` | out | Interrupt to host CPU/external processor for acceptance and fault events |
| `clk` | `clock` | in | Primary synchronous clock |
| `rst_n` | `reset` | in | Active-low reset |

## Ownership boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| SPI framing and register access | Owns | Consumes | Verifies bit accuracy and timing |
| Command validation and clamping | Owns | Supplies raw inputs | Verifies bounds and fallback behavior |
| Freshness / staleness decisions | Owns | Supplies timestamps/sequence metadata | Verifies timeout and stale-data cases |
| Actuator command emission | Owns final encoded output | Consumes `control_command` / `actuator_cmd_out` | Verifies output bounds and update timing |
| Fault/fallback signaling | Owns | Observes and reacts | Verifies fault codes and persistence rules |
| Audit logging schema | Owns firmware-side record fields | May ingest/export logs | Verifies presence and consistency of required fields |
| Geometry preprocessing inputs | Consumes or passes through as supported by implementation | Provides STL payload | Verifies accepted/rejected payload handling |
| Platform bring-up and power sequencing | Consumes platform state | Owns board-level policy | Verifies reset/ready sequencing |

## Assumptions
- The approved partition and RTL register collateral are stable and correspond to the bit maps listed above.
- The firmware runs on ESP32 under ESP-IDF using C and CMake.
- The FPGA-side SPI peripheral implements the stated mode 0, MSB-first, 25-byte frame contract.
- `geometry_input` may be delivered out-of-band from the SPI MMIO path if system integration uses separate preprocessing; the firmware contract only requires consistency with the validated control path.
- `stream_velocity_input` is constrained to the 20 to 55 m/s operating envelope; values outside the envelope shall be rejected or forced into fallback policy by firmware.
- The system may use either the register path or the optional bounded stream path, but not both as independent sources of truth for the same control cycle.
- `deployable_binary_ready: true` indicates the platform contract gate is ready; firmware release still depends on implementation conformance and validation passing.

## Validation hooks
- **Frame conformance test**: Verify SPI transactions are exactly 25 bytes, MSB-first, mode 0, with the specified bit packing and padding.
- **Timing test**: Confirm minimum 1 us interframe delay and maximum 10 MHz clock operation without protocol corruption.
- **Commit semantics test**: Drive command N, assert CS rise, and verify effect is committed only on CS deassertion; verify response N appears in frame N+2.
- **Register map test**: Read/write all defined MMIO fields and confirm `mmio_ready`, `mmio_rdata`, and write strobes behave per collateral.
- **Freshness test**: Present stale timestamps/sequence numbers in `model_or_reference_state` and confirm `freshness_status` and `fault_or_fallback_state` assert as specified.
- **Bounds test**: Provide out-of-range stream velocity and malformed command payloads; verify clamping, rejection, or fallback path is deterministic.
- **Traceability test**: Confirm each accepted or rejected command generates an audit record containing input summary, decision path, validation outcome, and emitted command.
- **IRQ test**: Verify `host_irq` asserts only for acceptance and fault events defined by the control logic, and is cleared/acknowledged per implemented register policy.
- **Reset recovery test**: Assert `rst_n` low, release reset, and confirm registers, status flags, and outputs return to defined safe defaults.
- **Compatibility test**: Attempt unsupported contract revisions and confirm firmware rejects or flags incompatibility rather than silently adapting bit fields.