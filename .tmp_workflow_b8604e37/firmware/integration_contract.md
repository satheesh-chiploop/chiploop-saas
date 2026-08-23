# Firmware Integration Contract

## 1) Contract Overview

- Target platform: `ulx3s_ecp5_45f_esp32` with `fpga_onboard_cpu` deployment architecture.
- Host MCU: ESP32 Xtensa LX6 using `esp-idf` and `cmake` build flow.
- Fabric link: SPI register transport from ESP32 controller to FPGA peripheral, mode 0, MSB-first, max 10 MHz.
- Transaction format is fixed: 39-byte full-duplex frames, with 7 leading padding bits and 2-frame response latency.
- Firmware responsibility is limited to transport, framing, register access, and contract-level status reporting; no device-layer jobs or interfaces were provided.
- The approved RTL collateral defines the bitmaps for input/output payloads and is the source of truth for wire encoding.
- Firmware must not claim deployable binary readiness unless the platform contract gate is satisfied.
- Integration is considered contract-complete only when frame encoding/decoding, timing, and response-latency behavior match the specified transport contract.

## 2) Contract Version + Compatibility Policy

**Contract version:** `chiploop.integration_contract.v1`

**Compatibility policy:**
- Backward compatibility is preserved for any revision that does not change:
  - frame size (`39 bytes`)
  - SPI mode (`0`)
  - frame order (`MSB-first`)
  - command/response latency model (`N+2`)
  - bit positions and widths in the approved bitmaps
- Any change to wire encoding, frame timing, or port map is a **breaking change** and requires a new major contract version.
- Firmware must reject or explicitly flag mismatched contract revisions at initialization time.
- Host/System software must treat unknown version values as incompatible unless an explicit compatibility waiver is present in the validation artifact.

## 3) Interfaces

### 3.1 Transport Interface

| Field | Value |
|---|---:|
| Transport | SPI |
| SPI mode | 0 |
| Clock polarity/phase | CPOL=0, CPHA=0 |
| Max clock | 10 MHz |
| Frame length | 39 bytes / 312 bits |
| Frame order | MSB-first |
| Chip select behavior | Command commits when CS rises |
| Inter-frame delay | Minimum 1 µs |
| Response latency | 2 frames |
| Command leading padding | 7 bits |
| Response trailing padding | 258 bits |

### 3.2 Serialized Input Map

| LSB | Port | Width |
|---:|---|---:|
| 0 | reg_valid | 1 |
| 1 | reg_we | 1 |
| 2 | reg_re | 1 |
| 3 | reg_addr | 8 |
| 11 | reg_wdata | 32 |
| 43 | reg_byte_en | 4 |
| 47 | req_valid | 1 |
| 48 | req_data | 128 |
| 176 | rsp_valid | 1 |
| 177 | rsp_data | 128 |

### 3.3 Serialized Output Map

| LSB | Port | Width |
|---:|---|---:|
| 0 | act_fault | 1 |
| 1 | act_cmd_hold | 1 |
| 2 | act_cmd | 16 |
| 18 | act_cmd_valid | 1 |
| 19 | rsp_ready | 1 |
| 20 | req_ready | 1 |
| 21 | reg_rdata | 32 |
| 53 | reg_ready | 1 |

### 3.4 Firmware API Surface

| API | Direction | Behavior |
|---|---|---|
| `fw_init()` | System -> FW | Initializes SPI peripheral, GPIO, and contract state; validates expected clock mode and frame sizing. |
| `fw_get_contract_version()` | System -> FW | Returns contract version string. |
| `fw_exchange_frame(const uint8_t *tx, uint8_t *rx)` | System -> FW | Sends one 39-byte SPI frame and captures the corresponding full-duplex response frame. |
| `fw_read_register(uint8_t addr, uint32_t *value)` | System -> FW | Issues register read using contract-defined payload fields. |
| `fw_write_register(uint8_t addr, uint32_t value, uint8_t byte_en)` | System -> FW | Issues register write using contract-defined payload fields. |
| `fw_get_status()` | System -> FW | Returns current transport/contract status and last error. |
| `fw_get_last_error()` | System -> FW | Returns last contract error code. |

### 3.5 Logging Schema

| Field | Type | Meaning |
|---|---|---|
| `ts_us` | integer | Monotonic timestamp in microseconds |
| `level` | string | `DEBUG`, `INFO`, `WARN`, `ERROR` |
| `component` | string | Fixed value: `fw_contract` |
| `event` | string | Event name such as `init_ok`, `frame_tx`, `frame_rx`, `contract_mismatch` |
| `code` | integer | Error or status code |
| `detail` | string | Human-readable diagnostic string |

### 3.6 Error Codes

| Code | Symbol | Meaning |
|---:|---|---|
| 0 | `FW_OK` | Success |
| 1 | `FW_ERR_UNSUPPORTED_CONTRACT` | Version or wire-format mismatch |
| 2 | `FW_ERR_SPI_CONFIG` | SPI configuration failure |
| 3 | `FW_ERR_FRAME_SIZE` | Frame length or serialization mismatch |
| 4 | `FW_ERR_TIMEOUT` | Transfer timeout or missing response window |
| 5 | `FW_ERR_PROTOCOL` | Invalid response validity / payload state |
| 6 | `FW_ERR_GPIO` | GPIO setup or pin-mux failure |
| 7 | `FW_ERR_INTERNAL` | Unclassified internal firmware error |

## 4) Ownership Boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| SPI transport setup | Owns | Observes | Verifies |
| Frame packing/unpacking | Owns | Consumes API | Verifies bit-accurate encoding |
| Register access sequencing | Owns | Requests via API | Verifies read/write correctness |
| Contract version handling | Owns | Must check compatibility | Verifies mismatch behavior |
| Logging format | Owns | May ingest | Verifies schema stability |
| Error code definitions | Owns | Must handle | Verifies coverage and mapping |
| Device-layer behavior | Not owned | Not owned | Out of scope unless separately specified |

## 5) Assumptions

- The approved RTL register collateral is authoritative for bit positions and field widths.
- `fw_init()` is expected to fail closed on contract mismatch rather than attempt best-effort operation.
- The ESP32 SPI peripheral can be configured to match the required mode 0 and MSB-first ordering.
- No DMA-specific behavior is mandated by the provided target refinement.
- No interrupt contract was provided; firmware shall not expose interrupt-dependent APIs in this contract.
- No power-mode contract was provided; firmware shall remain in default active operation unless extended later.
- The platform contract gate must be evaluated before any artifact is called deployable.

## 6) Validation Hooks

- **Wire-format test:** Capture MOSI/MISO and confirm 39-byte frame length, 7 leading padding bits, and MSB-first ordering.
- **Mode test:** Verify SPI mode 0 behavior on a logic analyzer: CPOL=0, CPHA=0.
- **Latency test:** Submit command `N` and confirm response `N+2` per transaction model.
- **Register access test:** Exercise read/write sequences and compare returned `reg_rdata` and `reg_ready` against expected RTL behavior.
- **Ready/fault test:** Validate `req_ready`, `rsp_ready`, `act_cmd_valid`, `act_fault`, and `act_cmd_hold` transitions under nominal and error cases.
- **Compatibility test:** Force mismatched contract version and confirm `FW_ERR_UNSUPPORTED_CONTRACT` with no partial operation.
- **Frame size test:** Deliberately alter serialized payload size and confirm firmware rejects with `FW_ERR_FRAME_SIZE`.
- **Logging test:** Confirm emitted logs match the required schema and include stable event names and numeric codes.
- **Boundary test:** Verify System/Host code only uses exported APIs and does not depend on private transport internals.