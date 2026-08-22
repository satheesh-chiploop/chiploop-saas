# firmware/integration_contract.md

## Contract overview
- Platform: `intelligent_active_aerodynamics_controller` on `ulx3s_ecp5_45f_esp32`, with ESP32 firmware controlling the FPGA over SPI register transport.
- Deployment architecture: `fpga_onboard_cpu`; the ESP32 is the firmware owner for transport, framing, register access, request/response sequencing, and fault handling.
- The FPGA exposes a compact memory-mapped control/status window via `reg_if` and control lines for framed software exchange.
- Command/response transport is SPI mode 0, MSB-first, 10 MHz max, with fixed 23-byte frames and explicit latency of 2 frames for responses.
- Control path includes `cmd_valid/cmd_ready` and `rsp_valid/rsp_ready` for host/software handshake across the SPI-mediated request workflow.
- Safety behavior is explicit: stale data, timeout, malformed response, or clamp fault forces `safe_fallback` and asserts `fault_irq`.
- `actuator_cmd` is a bounded 32-bit output encoding active-aero targets and optional mode bits; firmware must not emit unvalidated commands outside contract bounds.
- The host/software side owns geometry and vehicle-state intelligence; firmware transports, gates, and audits these inputs, but does not reinterpret model semantics beyond contract-defined framing.

## Contract version + compatibility policy
- **Contract schema:** `chiploop.application_intelligence.target_refinement.v1`
- **Contract status:** `resolved`
- **Versioning policy:**  
  - Backward-compatible changes may add reserved bits, telemetry fields, or validation metadata without changing frame width or bit positions.
  - Any change to frame size, bit offsets, timing assumptions, or safety semantics is a breaking change and requires a new contract version.
  - Firmware shall reject unknown or mismatched register map revisions unless explicitly marked compatible by the platform gate.
- **Compatibility rule:** firmware must match the approved partition and register collateral exactly; no runtime negotiation of field layout is implied by this contract.

## Interfaces

### External interface summary

| Name | Dir | Type | Width | Contract role |
|---|---:|---|---:|---|
| `geometry_input` | in | software_payload | 0 | STL geometry derived from DrivAerML reference geometry; managed by host/software, not exposed as raw top-level FPGA payload |
| `stream_velocity_input` | in | scalar | 32 | Operating stream velocity, valid operating range 20–55 m/s |
| `vehicle_state_stream` | in | software_stream | 0 | Vehicle state and aero-relevant inputs consumed by software-side control workflow |
| `reg_if` | inout | memory_mapped | 64 | Compact FPGA control/status register window for config, launch, status, and fault management |
| `cmd_valid` | out | control | 1 | Request framing valid signal from FPGA to external host/software path |
| `cmd_ready` | in | control | 1 | Host/software readiness indication for framed request acceptance |
| `rsp_valid` | in | control | 1 | Response availability signal from host/software back to FPGA |
| `rsp_ready` | out | control | 1 | FPGA acknowledgment of a validated response frame |
| `actuator_cmd` | out | actuator_bus | 32 | Bounded actuator command encoding active-aero targets and optional mode bits |
| `safe_fallback` | out | control | 1 | Asserted when controller must force safe aerodynamic configuration |
| `fault_irq` | out | interrupt | 1 | Signals stale-data, timeout, malformed response, or clamp fault to host |
| `trace_log` | out | software_trace | 0 | Traceable reference comparisons and control decision intermediates for validation and audit |
| `fault_injection_if` | in | test_control | 0 | Fault injection and test interface for stale-data and timeout verification |

### SPI transport contract

| Item | Value |
|---|---|
| Transport | `spi_mode_0_shift_transport` |
| Controller | ESP32 |
| Peripheral | FPGA |
| GPIO mapping | SCLK=14, CS_N=13, MOSI=15, MISO=2 |
| Max SPI clock | 10 MHz |
| Frame order | MSB-first |
| Command leading padding | 28 bits |
| Frame size | 184 bits / 23 bytes |
| Minimum interframe delay | 1 us |
| Response latency | 2 frames |
| Response trailing padding | 2 bits |
| Model | Command N commits on CS rising edge; response N is read in frame N+2 |

### Frame bit maps

#### Input bit map

| LSB | Port | Width |
|---:|---|---:|
| 0 | `mmio_valid` | 1 |
| 1 | `mmio_write` | 1 |
| 2 | `mmio_addr` | 8 |
| 10 | `mmio_wdata` | 64 |
| 74 | `cmd_ready` | 1 |
| 75 | `rsp_valid` | 1 |
| 76 | `rsp_data` | 80 |

#### Output bit map

| LSB | Port | Width |
|---:|---|---:|
| 0 | `fault_irq` | 1 |
| 1 | `safe_fallback` | 1 |
| 2 | `actuator_cmd_valid` | 1 |
| 3 | `actuator_cmd` | 32 |
| 35 | `rsp_ready` | 1 |
| 36 | `cmd_data` | 80 |
| 116 | `cmd_valid` | 1 |
| 117 | `mmio_ready` | 1 |
| 118 | `mmio_rdata` | 64 |

### Register access behavior
- `reg_if` is the firmware-visible control/status window for configuration, request launch, and status/fault management.
- Firmware shall treat `mmio_valid/mmio_write/mmio_addr/mmio_wdata` as the canonical register transaction fields for the FPGA register window.
- `mmio_ready` indicates acceptance of the register operation.
- `mmio_rdata` is valid only when returned with a read transaction and must be sampled according to the transport contract.
- `cmd_valid` and `rsp_ready` are driven by the FPGA-side contract logic; firmware must honor the handshake ordering and timing.

### Error and fault behavior
- `fault_irq` must assert for:
  - stale-data detection,
  - response timeout,
  - malformed response frame,
  - clamp fault.
- `safe_fallback` must assert whenever the controller cannot prove a valid actuator command.
- On fault, firmware must preserve deterministic state transitions and avoid issuing new active-aero commands until the fault is cleared by the approved recovery path.
- Invalid or out-of-range operating conditions, including velocity outside 20–55 m/s, must be handled as contract violations and forced into safe behavior.

## Ownership boundaries

| Area | Firmware ownership | System/Host ownership | Validation ownership |
|---|---|---|---|
| SPI framing and timing | Yes | No | Verify |
| Register read/write sequencing | Yes | No | Verify |
| Fault detection and safe fallback action | Yes | No | Verify |
| Geometry payload preparation | No | Yes | Verify interface compliance |
| Vehicle state generation | No | Yes | Verify interface compliance |
| Reference/surrogate workflow semantics | No | Yes | Verify with trace |
| Actuator command encoding | Yes, within contract | No | Verify bounds and format |
| Trace capture/export | Yes, contract-defined fields only | Consumes | Verify log completeness |
| Fault injection control | No | Test harness only | Owns |
| Platform gate approval for deployable binary | No | No | Owns |

## Assumptions
- The approved partition and RTL collateral already define the fixed register map and signal polarity used here.
- `geometry_input` and `vehicle_state_stream` are software-side constructs and are not serialized as raw top-level FPGA payloads beyond the approved transport path.
- `stream_velocity_input` is a 32-bit scalar input and its valid operating range is 20–55 m/s unless later expanded by a new contract version.
- The FPGA wrapper and ESP32 integration wrapper are ready and consistent with the stated SPI pinout and mode-0 transport.
- `firmware_gate.deployable_binary_ready` is reported as true, but no deployable binary should be claimed unless the platform contract gate is actually authorized in the integration environment.
- No DMA, power-mode, or interrupt subsystem contract is introduced beyond the specified signals and behaviors.

## Validation hooks
- **SPI frame conformance:** verify 23-byte frame length, MSB-first shifting, mode 0 polarity/phase, and 10 MHz ceiling.
- **Handshake compliance:** check `cmd_valid/cmd_ready` and `rsp_valid/rsp_ready` sequencing across the documented 2-frame response latency.
- **Register map compliance:** confirm `mmio_valid`, `mmio_write`, `mmio_addr`, `mmio_wdata`, `mmio_ready`, and `mmio_rdata` bit positions and widths match the collateral.
- **Safety behavior:** inject malformed response, timeout, and stale-data conditions via `fault_injection_if`; verify `safe_fallback=1` and `fault_irq=1`.
- **Clamp verification:** drive actuator command extremes and confirm bounded output behavior on `actuator_cmd`.
- **Velocity range enforcement:** test `stream_velocity_input` below 20 m/s and above 55 m/s; verify contract-violation handling and safe state.
- **Trace audit:** confirm `trace_log` captures reference comparisons and control decision intermediates needed for validation without exposing unsupported data paths.
- **Reset/recovery behavior:** verify the controller returns to a known safe state after fault clearance and does not emit unvalidated actuator commands.
- **Compatibility check:** mismatch the register map revision or frame sizing in a test harness and confirm firmware rejects the incompatibility rather than silently adapting.