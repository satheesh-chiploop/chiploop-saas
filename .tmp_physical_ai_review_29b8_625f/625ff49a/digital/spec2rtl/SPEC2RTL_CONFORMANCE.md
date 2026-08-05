# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 81
- Matched: 67
- Partial: 1
- Missing: 13
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-001 [missing]: Sample and register vehicle_geometry and flow_conditions inputs before any request generation.
- REQ-007 [missing]: Compute actuator targets from validated model outputs only; do not infer or encode physics or surrogate-model logic in RTL.
- REQ-008 [missing]: Clamp actuator outputs to programmable limits and optionally apply monotonic bounded rate limiting.
- REQ-010 [missing]: Provide registered fault and diagnostic outputs suitable for ASIC integration and system software polling.
- REQ-011 [partial]: All state changes shall occur only on clk edges; combinational feedback is forbidden.
- REQ-012 [missing]: vehicle_geometry shall be accepted only as framed metadata and payload descriptor storage; RTL shall not parse STL contents.
- REQ-014 [missing]: Inputs shall be sampled into internal registers before request issuance.
- REQ-019 [missing]: Validated model outputs shall be consumed only after matching sequence validation; no surrogate physics is embedded in RTL.
- REQ-020 [missing]: Actuator targets shall pass through per-channel clamp logic before output registration.
- REQ-022 [missing]: Optional rate limiting, if implemented by configuration, shall be monotonic and bounded by the per-channel delta limits.
- REQ-023 [missing]: actuator_command outputs shall be registered and glitch-free at the interface boundary.
- REQ-025 [missing]: The external model service interface remains runtime-independent and may connect to future NVIDIA-hosted NIM or ChipLoop GPU worker implementations without RTL changes.
- REQ-026 [missing]: All arithmetic used in control law shall be bounded, deterministic, and synthesizable in standard-cell ASIC flows.
