# Firmware Integration Contract

## 1) Contract overview

- Target platform: `ulx3s_ecp5_45f_esp32`
- Deployment architecture: `fpga_onboard_cpu`
- Host MCU: `esp32_xtensa_lx6` running `esp-idf`
- Fabric link: SPI register transport, mode 0, MSB-first, up to 10 MHz
- Frame format: 208-bit full-duplex transaction, 26 bytes per frame
- Command commit semantics: a command commits when `CS` rises; response `N` is read in frame `N+2`
- Register/port mapping is fixed by the provided transport contract bit maps
- Firmware gate status: portable source ready and deployable binary ready are both marked ready in the provided spec

## 2) Contract version + compatibility policy

**Contract version:** `chiploop.application_intelligence.firmware_integration_contract.v1`

**Compatibility policy:**
- Backward-compatible changes only within this version line
- Bit positions, frame length, chip-select commit behavior, and response latency are immutable for compatible firmware
- New ports may only be added in unused bits if they do not alter existing serialization or timing
- Any change to SPI mode, frame width, response latency, or command commit semantics requires a major version bump and explicit host validation
- Firmware must reject mismatched protocol versions during startup if version negotiation exists in the RTL collateral; otherwise it must expose the mismatch through status/error reporting without silent adaptation

## 3) Interfaces

### 3.1 SPI transport interface

| Item | Value |
|---|---|
| Bus | SPI |
| Mode | 0 |
| Clock polarity/phase | CPOL=0, CPHA=0 |
| Frame direction | Full-duplex |
| Frame length | 208 bits |
| Frame bytes | 26 |
| Bit order | MSB-first |
| Max clock | 10 MHz |
| Minimum inter-frame delay | 1 us |
| CS behavior | Rising edge commits command N |
| Response timing | Response N is returned in frame N+2 |
| Leading padding | 11 bits |
| Trailing padding | 4 bits |

### 3.2 Input bit map

| LSB | Width | Signal | Direction | Notes |
|---:|---:|---|---|---|
| 0 | 64 | `cfg_addr` | FW -> FPGA | Configuration address |
| 64 | 64 | `cfg_wdata` | FW -> FPGA | Configuration write data |
| 128 | 1 | `cfg_valid` | FW -> FPGA | Valid qualifier |
| 129 | 1 | `cfg_write` | FW -> FPGA | Write select |
| 130 | 1 | `model_req_ready` | FPGA -> FW | Host-visible readiness from FPGA side |
| 131 | 1 | `model_rsp_valid` | FPGA -> FW | Response valid from FPGA side |
| 132 | 64 | `model_rsp_data` | FPGA -> FW | Response payload |
| 196 | 1 | `external_fault_i` | FPGA -> FW | External fault indicator |

### 3.3 Output bit map

| LSB | Width | Signal | Direction | Notes |
|---:|---:|---|---|---|
| 140 | 64 | `cfg_rdata` | FPGA -> FW | Configuration read data |
| 139 | 1 | `cfg_ready` | FPGA -> FW | Ready for config access |
| 138 | 1 | `model_req_valid` | FPGA -> FW | Request valid to model side |
| 74 | 64 | `model_req_data` | FPGA -> FW | Request payload |
| 73 | 1 | `model_rsp_ready` | FW -> FPGA | Response backpressure control |
| 72 | 1 | `actuator_out_valid` | FPGA -> FW | Actuator output valid |
| 8 | 64 | `actuator_out_cmd` | FPGA -> FW | Actuator output command |
| 7 | 1 | `status_busy` | FPGA -> FW | Busy status |
| 6 | 1 | `status_accepted` | FPGA -> FW | Accepted status |
| 5 | 1 | `status_rejected_stale` | FPGA -> FW | Stale sequence reject |
| 4 | 1 | `status_rejected_seq` | FPGA -> FW | Sequence reject |
| 3 | 1 | `status_timeout` | FPGA -> FW | Timeout status |
| 2 | 1 | `status_fallback_active` | FPGA -> FW | Fallback path active |
| 1 | 1 | `status_clamped` | FPGA -> FW | Clamped output |
| 0 | 1 | `status_fault_summary` | FPGA -> FW | Aggregate fault summary |

### 3.4 Firmware API surface

| API | Direction | Behavior | Errors |
|---|---|---|---|
| `fw_spi_init()` | FW internal | Configure SPI mode 0, MSB-first, ≤10 MHz, GPIO mapping per target refinement | `ERR_CFG_INVALID`, `ERR_HW_INIT` |
| `fw_contract_selftest()` | FW internal | Verify frame size, bit packing, and static protocol assumptions before traffic | `ERR_CONTRACT_MISMATCH`, `ERR_HW_INIT` |
| `fw_tx_frame_build()` | FW internal | Serialize the 208-bit transaction according to the transport contract | `ERR_SERIALIZE_RANGE`, `ERR_CONTRACT_MISMATCH` |
| `fw_tx_frame_commit()` | FW internal | Assert CS, shift full frame, deassert CS to commit command | `ERR_SPI_TRANSFER`, `ERR_TIMEOUT` |
| `fw_rx_frame_parse()` | FW internal | Decode response bits from the returned frame and update local status | `ERR_DECODE`, `ERR_CONTRACT_MISMATCH` |
| `fw_get_status()` | FW/Host visible | Return last known status flags and error code | none |
| `fw_get_version()` | FW/Host visible | Return contract and firmware version identifiers | none |
| `fw_log_event()` | FW internal | Emit structured event records for init, transfer, fault, and protocol violations | none |
| `fw_set_power_mode()` | FW internal | Enter/exit supported low-power states without changing protocol semantics | `ERR_UNSUPPORTED_MODE` if not supported |

### 3.5 Logging schema

| Field | Type | Required | Description |
|---|---|---:|---|
| `ts_us` | u64 | yes | Monotonic timestamp in microseconds |
| `level` | enum | yes | `DEBUG`, `INFO`, `WARN`, `ERROR` |
| `module` | string | yes | Fixed module tag, e.g. `spi_transport` |
| `event` | string | yes | Short event name |
| `seq` | u64 | yes | Transaction sequence number |
| `status` | u32 | yes | Packed status/error summary |
| `detail` | u64 | no | Auxiliary data payload |

### 3.6 Error codes

| Code | Meaning |
|---|---|
| `ERR_OK` | No error |
| `ERR_CFG_INVALID` | Invalid SPI or GPIO configuration |
| `ERR_HW_INIT` | Hardware initialization failed |
| `ERR_CONTRACT_MISMATCH` | Frame size, bit layout, or timing mismatch |
| `ERR_SERIALIZE_RANGE` | Field value exceeds allocated width |
| `ERR_DECODE` | Received frame could not be parsed |
| `ERR_SPI_TRANSFER` | SPI transaction failed |
| `ERR_TIMEOUT` | Expected response not observed in time |
| `ERR_UNSUPPORTED_MODE` | Requested power mode is unsupported |

## 4) Ownership boundaries

| Area | Firmware | System/Host | Validation |
|---|---|---|---|
| SPI peripheral setup on ESP32 | Owns | Does not own | Verifies pinout, mode, and clock limits |
| Frame packing/unpacking | Owns | Consumes API only | Checks bit-accurate serialization |
| Protocol timing enforcement | Owns | Must respect timing contract | Measures CS commit and inter-frame delay |
| Status interpretation | Owns status generation | Owns user-facing policy | Confirms status flag mapping |
| Error code definition | Owns firmware-side codes | Maps to application behavior | Confirms code stability |
| Logging schema emission | Owns | Can ingest logs | Validates schema completeness |
| FPGA register semantics | Does not own | Does not own | Validates against RTL collateral |
| Deployment gating | Does not own | Does not own | Confirms platform contract readiness before release |

## 5) Assumptions

- The provided bit maps are authoritative and complete for the current firmware scope
- SPI is the only required transport for the selected board integration path
- No additional device-layer jobs or interfaces are in scope beyond the specified SPI register transport
- The ESP32 firmware uses `esp-idf` and CMake as specified
- The FPGA-side serialization is already aligned to the stated 208-bit transaction model
- Response latency of 2 frames is fixed and must not be optimized away in firmware
- No deployable binary should be claimed unless the platform contract gate remains ready at build/release time

## 6) Validation hooks

- **Static layout check:** verify all packed fields match the specified LSB positions and widths
- **Frame length check:** confirm every transaction is exactly 26 bytes / 208 bits
- **Mode check:** confirm SPI mode 0, MSB-first, and SCLK ≤ 10 MHz
- **CS commit check:** scope CS rise behavior and confirm command commit occurs only on deassertion
- **Latency check:** inject a known command and verify response is observed in frame `N+2`
- **Read/write sanity:** test `cfg_valid`/`cfg_write` combinations against expected `cfg_ready` and `cfg_rdata` behavior
- **Status flag check:** exercise nominal, busy, accepted, rejected, timeout, fallback, clamped, and fault cases and confirm correct bit assertions
- **Fault propagation check:** assert `external_fault_i` and confirm `status_fault_summary` reflects the fault condition
- **Version check:** compare firmware-reported version identifiers with the approved contract version before enabling host traffic
- **Regression hook:** replay captured SPI traces and compare byte-for-byte against expected serialization