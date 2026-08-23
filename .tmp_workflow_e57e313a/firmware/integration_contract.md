# Firmware Integration Contract

## 1) Contract overview

- Target platform is **ulx3s_ecp5_45f_esp32** with **ESP32 (esp-idf/CMake/C)** as the hard CPU and **FPGA fabric over SPI register transport** as the peripheral interface.
- The integration wrapper is marked **ready**; firmware is expected to interact with the FPGA via the approved **SPI mode 0**, **MSB-first**, full-duplex register-frame contract.
- The transport uses **26-byte frames** with **11 leading padding bits**, **2-frame response latency**, and **4 trailing padding bits** on output serialization.
- Firmware owns **host-side transaction formation, chip-select framing, pacing, and validation of response timing/format**; it does not own FPGA register semantics beyond the published bit map.
- The contract supports **configuration writes, configuration reads, model request/response handshaking, actuator command emission, and status/error observation** through the serialized frame fields.
- The platform gate is marked ready for portable source and deployable binary, but this document only defines the **integration contract**, not a deployment claim.
- No device-layer jobs or extra interfaces were declared; contract scope is limited to the SPI register path and global firmware integration behaviors.

## 2) Contract version + compatibility policy

**Contract version:** `chiploop.application_intelligence.target_refinement.v1`  
**Compatibility policy:**
- **Backward-compatible** changes may add reserved bits/fields, additional status codes, or non-breaking logging fields without changing frame size, polarity, or timing contract.
- **Breaking** changes include any modification to:
  - frame length (`26 bytes`)
  - SPI mode (`0`)
  - bit ordering (`MSB-first`)
  - response latency (`2 frames`)
  - bit allocations in the approved input/output bit maps
  - minimum inter-frame delay
- Firmware must treat unspecified bits as **reserved/ignore** and must not depend on them for correctness.
- Host/system software must reject mismatched protocol versions unless an explicit compatibility override is documented and validated.

## 3) Interfaces

### 3.1 Transport interface

| Item | Contract |
|---|---|
| Physical link | SPI |
| SPI mode | 0 |
| Bit order | MSB-first |
| Maximum clock | 10 MHz |
| Frame size | 26 bytes / 208 bits |
| Minimum inter-frame delay | 1 us |
| CS behavior | Command N commits on CS rising edge |
| Response timing | Response N is read in frame N+2 |
| Padding | 11 leading input padding bits; 4 trailing output padding bits |

### 3.2 Input bit map

| LSB | Width | Port | Direction | Notes |
|---:|---:|---|---|---|
| 0 | 64 | cfg_addr | FW -> FPGA | Configuration address |
| 64 | 64 | cfg_wdata | FW -> FPGA | Configuration write data |
| 128 | 1 | cfg_valid | FW -> FPGA | Valid strobe |
| 129 | 1 | cfg_write | FW -> FPGA | Write qualifier |
| 130 | 1 | model_req_ready | FW -> FPGA | Host-side ready indication into fabric |
| 131 | 1 | model_rsp_valid | FW -> FPGA | Host-side response-valid indication into fabric |
| 132 | 64 | model_rsp_data | FW -> FPGA | Response payload input to fabric |
| 196 | 1 | external_fault_i | FW -> FPGA | External fault input |

### 3.3 Output bit map

| LSB | Width | Port | Direction | Notes |
|---:|---:|---|---|---|
| 140 | 64 | cfg_rdata | FPGA -> FW | Configuration read data |
| 139 | 1 | cfg_ready | FPGA -> FW | Configuration interface ready |
| 138 | 1 | model_req_valid | FPGA -> FW | Request valid to host |
| 74 | 64 | model_req_data | FPGA -> FW | Request payload |
| 73 | 1 | model_rsp_ready | FPGA -> FW | Response ready from fabric |
| 72 | 1 | actuator_out_valid | FPGA -> FW | Actuator output valid |
| 8 | 64 | actuator_out_cmd | FPGA -> FW | Actuator command payload |
| 7 | 1 | status_busy | FPGA -> FW | Busy indication |
| 6 | 1 | status_accepted | FPGA -> FW | Transaction accepted |
| 5 | 1 | status_rejected_stale | FPGA -> FW | Rejected due to stale sequence/context |
| 4 | 1 | status_rejected_seq | FPGA -> FW | Sequence error |
| 3 | 1 | status_timeout | FPGA -> FW | Timeout indicator |
| 2 | 1 | status_fallback_active | FPGA -> FW | Fallback mode active |
| 1 | 1 | status_clamped | FPGA -> FW | Clamped output/data |
| 0 | 1 | status_fault_summary | FPGA -> FW | Aggregate fault summary |

### 3.4 Firmware-facing API contract

| API | Ownership | Required behavior |
|---|---|---|
| `fw_spi_init()` | FW | Configure SPI mode 0, MSB-first, ≤10 MHz, GPIO mapping per target |
| `fw_spi_txrx_frame(tx, rx)` | FW | Shift exactly 26 bytes per transaction and preserve CS framing |
| `fw_cfg_write(addr, wdata)` | FW | Emit config write transaction; set `cfg_valid=1`, `cfg_write=1` |
| `fw_cfg_read(addr)` | FW | Emit config read transaction; sample `cfg_rdata` from aligned response frame |
| `fw_model_submit(req_data)` | FW | Present request/response handshake fields per contract timing |
| `fw_get_status()` | FW | Decode status bits from the latest valid response frame |
| `fw_fault_set(external_fault_i)` | FW | Drive external fault input deterministically |
| `fw_log_event(code, fields...)` | FW | Emit structured logs using the contract schema below |

### 3.5 Error codes

| Code | Name | Meaning | Action |
|---|---|---|---|
| 0x00 | `FW_OK` | No error | Continue |
| 0x01 | `FW_ERR_SPI_MODE` | SPI configuration mismatch | Fail init |
| 0x02 | `FW_ERR_FRAME_LEN` | Frame length mismatch | Reject transaction |
| 0x03 | `FW_ERR_TIMING` | Inter-frame or response timing violation | Retry or fail |
| 0x04 | `FW_ERR_PROTOCOL` | Bit-map/protocol violation | Reject transaction |
| 0x05 | `FW_ERR_FPGA_FAULT` | `status_fault_summary=1` | Escalate to host |
| 0x06 | `FW_ERR_TIMEOUT` | No valid response within expected latency | Retry or fail |
| 0x07 | `FW_ERR_NOT_READY` | `cfg_ready=0` or fabric not ready | Defer operation |

### 3.6 Logging schema

| Field | Type | Required | Description |
|---|---|---:|---|
| `ts_us` | integer | yes | Monotonic timestamp in microseconds |
| `level` | string | yes | `debug` / `info` / `warn` / `error` |
| `event` | string | yes | Stable event name |
| `code` | integer | yes | Contract error/status code |
| `seq` | integer | yes | Firmware transaction sequence counter |
| `spi_len` | integer | yes | Bytes transferred |
| `status_bits` | integer | yes | Decoded output status field |
| `cfg_addr` | integer | no | Logged on config transactions |
| `cfg_write` | boolean | no | Logged on config transactions |
| `fault` | boolean | no | External fault state |

## 4) Ownership boundaries

| Area | Firmware | System/Host software | Validation |
|---|---|---|---|
| SPI electrical/config | Owns setup and operation on ESP32 | Consumes API only | Verifies clock/mode/pin compliance |
| Frame packing/unpacking | Owns serialization/deserialization | May call APIs; must not reinterpret bits | Checks bit alignment and width |
| Protocol timing | Owns CS framing and delay enforcement | Must tolerate contract latency | Measures inter-frame and response latency |
| FPGA register semantics | Not owned | Not owned | Defined by RTL collateral and testbench |
| Error handling/logging | Owns local codes and structured logs | Must ingest logs and react | Confirms code mapping and observability |
| Deployment gating | Must not claim binary readiness beyond gate | Consumes artifacts | Confirms gate state before release |

## 5) Assumptions

- The ESP32 runs **ESP-IDF** with **CMake** and uses the target `esp32`.
- The FPGA register collateral provided in the evidence source is authoritative for the listed bit map and timing parameters.
- `cfg_ready` is the primary readiness indicator for configuration transactions.
- Reserved bits are ignored by both sides unless a later contract version defines them.
- The system tolerates a **2-frame delayed response model** and firmware will not shortcut that latency.
- No interrupt, DMA, or power-mode extensions are assumed beyond the explicit transport and logging behaviors here.
- The platform contract gate status must be checked before any release or binary claim.

## 6) Validation hooks

- **SPI mode and framing test:** Verify CPOL/CPHA = mode 0, MSB-first ordering, 26-byte exact transfers, and CS-rising-edge commit behavior.
- **Latency test:** Send a known command in frame N and confirm its response appears in frame N+2.
- **Bit-map conformance test:** Exercise each mapped field independently and confirm correct lane placement in serialized frames.
- **Ready-path test:** Hold `cfg_ready=0` and verify firmware defers or rejects config operations with `FW_ERR_NOT_READY`.
- **Fault-path test:** Assert `external_fault_i` and verify `status_fault_summary` and logging escalation.
- **Read/write symmetry test:** Write a config location, then read it back and confirm `cfg_rdata` matches expected behavior from RTL collateral.
- **Timing margin test:** Run at ≤10 MHz and verify minimum 1 us inter-frame delay is respected under load.
- **Logging compliance test:** Confirm every protocol error emits a structured log record containing `ts_us`, `event`, `code`, `seq`, and `status_bits`.